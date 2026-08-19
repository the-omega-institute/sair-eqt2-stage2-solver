#!/usr/bin/env python3
"""Solo solver for SAIR-EQT2 Stage 2 — deterministic floor + gpt-oss-120b fallback.

Single-file, official stdin/stdout JSON protocol. Three escalating passes:

  Pass 1 (deterministic, no LLM): finite-magma counterexample for the false branch
    (brute Fin 2-3, F_p linear p<=7, F_2^2/Fin 4 matrix-linear and Z_n polynomial
    via finOpTable; then linear/affine mod n <= 50, F_3^2 / F_2^3 matrix-linear and
    polynomial ops certified through an arithmetic `submission.op` on Fin n; canned
    ℕ-carrier models for Austin pairs; a SEM-style finite model finder with Latin
    propagation for carriers 4..10).
  Pass 2 (deterministic, no LLM): singleton true proof, then substitution-instance
    (Birkhoff) true proof.
  Pass 3 (LLM): the organizer proxy calls openai/gpt-oss-120b with the top-level
    PROMPT template; the solver parses the returned JSON verdict, builds the Lean
    certificate with the SAME make_true_code / make_false_code helpers as the floor,
    submits it to the judge, and iterates on judge feedback ({history.attempts})
    until the proxy reports the budget is spent.

Every candidate is judge-verified; the solver never fabricates an accepted verdict.
The LLM template is the top-level PROMPT constant, extracted by the proxy via AST.
"""

# Extracted by the proxy (AST) and filled with {problem.*}/{solver.*}/{history.*}.
PROMPT = """You are an expert Lean 4 proof engineer solving equational-implication problems over magmas.

A magma is a type G with one binary operation written ◇ (infix, left-associative). Decide whether
Hypothesis {problem.equation1_id}:  {problem.equation1}
implies
Goal {problem.equation2_id}:  {problem.equation2}
universally, i.e. for EVERY magma G and all values of the variables.

A fast deterministic search already ran on our side (see the solver hint). If it found NO counterexample
among all magmas of size <= 3, all F_p-linear magmas (p <= 7), and all F_2^2 (Fin 4) matrix-linear magmas,
the implication is very likely TRUE and you should build a rewriting proof. If a small counterexample is
plausible, give one instead.

Solver hint: {solver.hint}

Reply with ONLY ONE JSON object. No markdown fences, no commentary before or after.

TRUE case -- give the Lean 4 tactic body that closes the goal. Your body runs immediately after
`intro G _ h`, so in scope you have:
  * `h`  : the hypothesis as a universally quantified equation. Apply it to concrete terms, e.g.
           `h a b c`, to obtain an equation instance; use `.symm` to flip an equality.
  * the operation is the infix `◇`. Close the goal by rewriting: `rw`, `calc`, `simp only [...]`,
    `exact`. For a pure equational goal you need only `h` and `◇` -- no external lemmas.
  Respond exactly: {"verdict":"true","proof":"<tactic lines, separated by \\n>"}

FALSE case -- give a finite counterexample magma as a Cayley table on Fin N with N <= 10. The table is
`table[i][j] = i ◇ j`, entries are single digits 0..N-1, the hypothesis must hold on it and the goal
must fail. Keep N as small as possible.
  Respond exactly: {"verdict":"false","counterexample_table":[[...],[...]]}

Previous attempts and the judge's errors (read these and fix exactly what was rejected):
{history.attempts}
"""

# Safety cap so a model that keeps returning parseable-but-wrong answers cannot spin
# forever in local runs; in the official harness the wall-clock/token budget stops the
# loop first (the proxy then returns {"error": ...}).
MAX_LLM_ROUNDS = 16

import json
import re
import sys
import heapq
import itertools
import time
from collections import deque
from itertools import product
from time import monotonic


VAR_ORDER = tuple("abcdefghijklmnopqrstuvwxyz")
# finOpTable only parses single-digit entries correctly.
PRIMES = (2, 3, 5, 7)
AFFINE_PRIMES = (2, 3, 5, 7)
AFFINE_CANDIDATE_LIMIT = 80000
F2_MATRICES_2 = tuple(
    (
        ((bits >> 0) & 1, (bits >> 1) & 1),
        ((bits >> 2) & 1, (bits >> 3) & 1),
    )
    for bits in range(16)
)
F2_ZERO_2 = ((0, 0), (0, 0))
F2_ID_2 = ((1, 0), (0, 1))
F2_VECTORS_2 = ((0, 0), (1, 0), (0, 1), (1, 1))


class ParseError(ValueError):
    pass


def read_message():
    line = sys.stdin.readline()
    if not line:
        sys.exit(0)
    return json.loads(line.strip())


def send_message(msg):
    print(json.dumps(msg), flush=True)


def call_judge(verdict, code):
    send_message({"call": "judge", "verdict": verdict, "code": code})
    return read_message()


def call_llm(context):
    # Proxy fills the top-level PROMPT template ({problem.*}/{history.*}/{solver.*})
    # and returns {"response": <model text>} or {"error": <reason>}.
    send_message({"call": "llm", "context": context})
    return read_message()


def extract_json(text):
    # gpt-oss-120b sometimes wraps output in <think>...</think> or ```json fences.
    text = re.sub(r"<think>[\s\S]*?</think>", "", text).strip()
    text = re.sub(r"^```(?:json)?\s*\n?", "", text)
    text = re.sub(r"\n?```\s*$", "", text)
    try:
        return json.loads(text.strip())
    except Exception:
        pass
    m = re.search(r"\{[\s\S]*\}", text)
    if m:
        try:
            return json.loads(m.group())
        except Exception:
            pass
    return None


def clean_proof_body(body):
    # Strip anything the model added around the bare tactic body: a leading
    # `:= by` / `by`, stray `import` lines, and surrounding whitespace.
    if ":= by" in body:
        body = re.sub(r"^.*?:=\s*by\s*\n?", "", body, count=1, flags=re.DOTALL)
    body = re.sub(r"^\s*by\s+", "", body)
    body = re.sub(r"^\s*import\s+.*\n?", "", body, flags=re.MULTILINE)
    body = body.strip()
    # make_true_code always prepends `intro G _ h`, so a model-reemitted copy of
    # that exact binder line is redundant and causes introN failures. Strip only
    # a leading `intro G _ h` (whitespace-tolerant); never `intro x` / other intros.
    body = re.sub(r"^intro\s+G\s+_\s+h\s*(?:\n|$)", "", body, count=1)
    return body.strip()


def valid_llm_table(tbl):
    # finOpTable only parses single-digit entries, so N<=10; require a square
    # table whose entries are in range. Rejects a known-bad cert before we spend
    # a judge call on it.
    if not isinstance(tbl, list) or not (1 <= len(tbl) <= 10):
        return False
    n = len(tbl)
    for row in tbl:
        if not isinstance(row, list) or len(row) != n:
            return False
        for v in row:
            if not isinstance(v, int) or not (0 <= v < n):
                return False
    return True


def deterministic_hint(eq1_text, eq2_text):
    # Tell the model what our floor already ruled out, so it can lean TRUE when the
    # small/linear counterexample space is exhausted.
    try:
        found = search_counterexample(eq1_text, eq2_text, use_linear=True)
    except Exception:
        found = None
    if found is not None:
        return ("a deterministic counterexample WAS found by our floor but the judge did not accept it; "
                "re-examine: the implication is most likely FALSE, refine the finite counterexample")
    return ("no counterexample exists among all magmas of size <= 3, all F_p-linear magmas (p <= 7), "
            "or F_2^2 (Fin 4) matrix-linear magmas -> the implication is very likely TRUE; build a "
            "rewriting proof from h")


def tokenize(source):
    tokens = []
    i = 0
    while i < len(source):
        ch = source[i]
        if ch.isspace():
            i += 1
        elif ch in "()=":
            tokens.append(ch)
            i += 1
        elif ch == "\u25c7":
            tokens.append("D")
            i += 1
        elif "a" <= ch <= "z":
            tokens.append(ch)
            i += 1
        else:
            raise ParseError("unexpected character %r" % ch)
    return tokens


class Parser:
    def __init__(self, text):
        self.tokens = tokenize(text)
        self.pos = 0

    def peek(self):
        if self.pos >= len(self.tokens):
            return None
        return self.tokens[self.pos]

    def take(self, token=None):
        got = self.peek()
        if got is None:
            raise ParseError("unexpected end of input")
        if token is not None and got != token:
            raise ParseError("expected %r, got %r" % (token, got))
        self.pos += 1
        return got

    def parse_equation(self):
        left = self.parse_expr()
        self.take("=")
        right = self.parse_expr()
        if self.peek() is not None:
            raise ParseError("trailing token %r" % self.peek())
        variables = []
        seen = set()
        collect_vars(left, seen, variables)
        collect_vars(right, seen, variables)
        return {"left": left, "right": right, "variables": variables}

    def parse_expr(self):
        left = self.parse_atom()
        while self.peek() == "D":
            self.take("D")
            right = self.parse_atom()
            left = ("op", left, right)
        return left

    def parse_atom(self):
        token = self.peek()
        if token is None:
            raise ParseError("unexpected end of term")
        if token == "(":
            self.take("(")
            term = self.parse_expr()
            self.take(")")
            return term
        if len(token) == 1 and "a" <= token <= "z":
            self.take()
            return ("var", token)
        raise ParseError("unexpected token %r" % token)


def parse_equation(text):
    return Parser(text).parse_equation()


def collect_vars(term, seen, out):
    if term[0] == "var":
        if term[1] not in seen:
            seen.add(term[1])
            out.append(term[1])
        return
    collect_vars(term[1], seen, out)
    collect_vars(term[2], seen, out)


def eval_term(term, env, op):
    if term[0] == "var":
        return env[term[1]]
    return op(eval_term(term[1], env, op), eval_term(term[2], env, op))


def equation_holds(eq, n, op):
    variables = eq["variables"]
    for vals in product(range(n), repeat=len(variables)):
        env = dict(zip(variables, vals))
        if eval_term(eq["left"], env, op) != eval_term(eq["right"], env, op):
            return False
    return True


def equation_fails(eq, n, op):
    variables = eq["variables"]
    for vals in product(range(n), repeat=len(variables)):
        env = dict(zip(variables, vals))
        if eval_term(eq["left"], env, op) != eval_term(eq["right"], env, op):
            return True
    return False


def table_to_op(table):
    return lambda a, b: table[a][b]


def exhaustive_tables(n):
    total = n ** (n * n)
    for enc in range(total):
        x = enc
        table = []
        for _i in range(n):
            row = []
            for _j in range(n):
                row.append(x % n)
                x //= n
            table.append(row)
        yield table


def brute_counterexample(eq1, eq2, max_n=3):
    for n in range(2, max_n + 1):
        for table in exhaustive_tables(n):
            op = table_to_op(table)
            if equation_holds(eq1, n, op) and equation_fails(eq2, n, op):
                return {"stage": "brute", "n": n, "table": table}
    return None


def linear_coeffs(term, p, a, b):
    if term[0] == "var":
        return {term[1]: 1 % p}
    left = linear_coeffs(term[1], p, a, b)
    right = linear_coeffs(term[2], p, a, b)
    out = {}
    for var, coeff in left.items():
        out[var] = (out.get(var, 0) + a * coeff) % p
    for var, coeff in right.items():
        out[var] = (out.get(var, 0) + b * coeff) % p
    return {var: coeff for var, coeff in out.items() if coeff % p}


def coeff_delta(eq, p, a, b):
    left = linear_coeffs(eq["left"], p, a, b)
    right = linear_coeffs(eq["right"], p, a, b)
    variables = set(left) | set(right)
    return {v: (left.get(v, 0) - right.get(v, 0)) % p for v in variables}


def linear_equation_holds(eq, p, a, b):
    return all(value == 0 for value in coeff_delta(eq, p, a, b).values())


def linear_equation_fails(eq, p, a, b):
    return any(value != 0 for value in coeff_delta(eq, p, a, b).values())


def linear_table(p, a, b):
    return [[(a * i + b * j) % p for j in range(p)] for i in range(p)]


def linear_counterexample(eq1, eq2):
    for p in PRIMES:
        for a in range(p):
            for b in range(p):
                if linear_equation_holds(eq1, p, a, b) and linear_equation_fails(eq2, p, a, b):
                    return {"stage": "linear", "n": p, "a": a, "b": b, "table": linear_table(p, a, b)}
    return None


def affine_coeffs(term, p, a, b, c):
    if term[0] == "var":
        return {term[1]: 1 % p}, 0
    left, left_const = affine_coeffs(term[1], p, a, b, c)
    right, right_const = affine_coeffs(term[2], p, a, b, c)
    out = {}
    for var, coeff in left.items():
        out[var] = (out.get(var, 0) + a * coeff) % p
    for var, coeff in right.items():
        out[var] = (out.get(var, 0) + b * coeff) % p
    const = (a * left_const + b * right_const + c) % p
    return {var: coeff for var, coeff in out.items() if coeff % p}, const


def affine_delta(eq, p, a, b, c):
    left, left_const = affine_coeffs(eq["left"], p, a, b, c)
    right, right_const = affine_coeffs(eq["right"], p, a, b, c)
    variables = set(left) | set(right)
    delta = {v: (left.get(v, 0) - right.get(v, 0)) % p for v in variables}
    delta[""] = (left_const - right_const) % p
    return delta


def affine_equation_holds(eq, p, a, b, c):
    return all(value == 0 for value in affine_delta(eq, p, a, b, c).values())


def affine_equation_fails(eq, p, a, b, c):
    return any(value != 0 for value in affine_delta(eq, p, a, b, c).values())


def affine_table(p, a, b, c):
    return [[(a * i + b * j + c) % p for j in range(p)] for i in range(p)]


def affine_counterexample(eq1, eq2):
    tested = 0
    for p in AFFINE_PRIMES:
        for a in range(p):
            for b in range(p):
                if tested >= AFFINE_CANDIDATE_LIMIT:
                    return None
                tested += 1
                # With no constants in the input language, all nonzero affine
                # offsets have the same equational hold/fail behavior.
                c = 1
                if affine_equation_holds(eq1, p, a, b, c) and affine_equation_fails(eq2, p, a, b, c):
                    return {
                        "stage": "affine",
                        "n": p,
                        "a": a,
                        "b": b,
                        "c": c,
                        "table": affine_table(p, a, b, c),
                    }
    return None


def f2_mat_add(x, y):
    return (
        (x[0][0] ^ y[0][0], x[0][1] ^ y[0][1]),
        (x[1][0] ^ y[1][0], x[1][1] ^ y[1][1]),
    )


def f2_mat_mul(x, y):
    return (
        (
            (x[0][0] & y[0][0]) ^ (x[0][1] & y[1][0]),
            (x[0][0] & y[0][1]) ^ (x[0][1] & y[1][1]),
        ),
        (
            (x[1][0] & y[0][0]) ^ (x[1][1] & y[1][0]),
            (x[1][0] & y[0][1]) ^ (x[1][1] & y[1][1]),
        ),
    )


def f2_mat_vec_mul(x, v):
    return (
        (x[0][0] & v[0]) ^ (x[0][1] & v[1]),
        (x[1][0] & v[0]) ^ (x[1][1] & v[1]),
    )


def f2_vec_add(x, y):
    return (x[0] ^ y[0], x[1] ^ y[1])


def f2_matrix_coeffs(term, a, b):
    if term[0] == "var":
        return {term[1]: F2_ID_2}, (0, 0)
    left, left_const = f2_matrix_coeffs(term[1], a, b)
    right, right_const = f2_matrix_coeffs(term[2], a, b)
    out = {}
    for var, coeff in left.items():
        out[var] = f2_mat_add(out.get(var, F2_ZERO_2), f2_mat_mul(a, coeff))
    for var, coeff in right.items():
        out[var] = f2_mat_add(out.get(var, F2_ZERO_2), f2_mat_mul(b, coeff))
    const = f2_vec_add(f2_mat_vec_mul(a, left_const), f2_mat_vec_mul(b, right_const))
    return {var: coeff for var, coeff in out.items() if coeff != F2_ZERO_2}, const


def f2_matrix_affine_coeffs(term, a, b, c):
    coeffs, const = f2_matrix_coeffs(term, a, b)
    if term[0] == "var":
        return coeffs, const
    return coeffs, f2_vec_add(const, c)


def f2_matrix_delta(eq, a, b, c=None):
    coeff_fn = f2_matrix_coeffs if c is None else f2_matrix_affine_coeffs
    if c is None:
        left, left_const = coeff_fn(eq["left"], a, b)
        right, right_const = coeff_fn(eq["right"], a, b)
    else:
        left, left_const = coeff_fn(eq["left"], a, b, c)
        right, right_const = coeff_fn(eq["right"], a, b, c)
    variables = set(left) | set(right)
    delta = {v: f2_mat_add(left.get(v, F2_ZERO_2), right.get(v, F2_ZERO_2)) for v in variables}
    delta[""] = f2_vec_add(left_const, right_const)
    return delta


def f2_matrix_equation_holds(eq, a, b, c=None):
    return all(value == F2_ZERO_2 or value == (0, 0) for value in f2_matrix_delta(eq, a, b, c).values())


def f2_matrix_equation_fails(eq, a, b, c=None):
    return any(value != F2_ZERO_2 and value != (0, 0) for value in f2_matrix_delta(eq, a, b, c).values())


def f2_matrix_counterexample(eq1, eq2, use_affine=True):
    for a in F2_MATRICES_2:
        for b in F2_MATRICES_2:
            if f2_matrix_equation_holds(eq1, a, b) and f2_matrix_equation_fails(eq2, a, b):
                return {"stage": "f2_matrix", "n": 4, "a_mat": a, "b_mat": b}
    if use_affine:
        for a in F2_MATRICES_2:
            for b in F2_MATRICES_2:
                for c in F2_VECTORS_2[1:]:
                    if f2_matrix_equation_holds(eq1, a, b, c) and f2_matrix_equation_fails(eq2, a, b, c):
                        return {"stage": "f2_matrix_affine", "n": 4, "a_mat": a, "b_mat": b, "c_vec": c}
    return None


# finOpTable parses only single-digit entries, so any emitted witness must live
# on Fin n with n <= 10 (entries 0..9). The polynomial families below stay within
# that cap; carriers with n >= 11 are unreachable contestant-side (see
# SUBSTRATE_NOTES.md) and are never generated.
POLY_MAX_N = 10          # single-digit finOpTable cap
POLY_QUAD_MAX_N = 6      # quadratic family: n^6 coefficient grid, keep small


def _poly_table(n, coeffs):
    c0, a, b, d, e, f = coeffs
    return [[(c0 + a * i + b * j + d * i * j + e * i * i + f * j * j) % n
             for j in range(n)] for i in range(n)]


def polynomial_counterexample(eq1, eq2):
    # Structured Z_n magmas the linear/F2^2 stages miss: full linear and affine
    # over ALL n <= 10 (not just primes 2,3,5,7), then low-degree quadratic over
    # small n. Uses the exact equation_holds/equation_fails table check whose
    # finOpTable certificate the official judge accepts. Returns a witness dict
    # carrying the concrete table, or None.
    # linear a*i + b*j over every n <= 10
    for n in range(2, POLY_MAX_N + 1):
        for a in range(n):
            for b in range(n):
                op = table_to_op(_poly_table(n, (0, a, b, 0, 0, 0)))
                if equation_holds(eq1, n, op) and equation_fails(eq2, n, op):
                    return {"stage": "poly_linear", "n": n, "table": _poly_table(n, (0, a, b, 0, 0, 0))}
    # affine a*i + b*j + c over every n <= 10
    for n in range(2, POLY_MAX_N + 1):
        for a in range(n):
            for b in range(n):
                for c in range(1, n):
                    op = table_to_op(_poly_table(n, (c, a, b, 0, 0, 0)))
                    if equation_holds(eq1, n, op) and equation_fails(eq2, n, op):
                        return {"stage": "poly_affine", "n": n, "table": _poly_table(n, (c, a, b, 0, 0, 0))}
    # quadratic c0 + a*i + b*j + d*ij + e*i^2 + f*j^2 over small n
    for n in range(2, POLY_QUAD_MAX_N + 1):
        rng = range(n)
        for a in rng:
            for b in rng:
                for d in rng:
                    for e in rng:
                        for f in rng:
                            for c0 in rng:
                                coeffs = (c0, a, b, d, e, f)
                                op = table_to_op(_poly_table(n, coeffs))
                                if equation_holds(eq1, n, op) and equation_fails(eq2, n, op):
                                    return {"stage": "poly_quadratic", "n": n, "table": _poly_table(n, coeffs)}
    return None


# ---------------------------------------------------------------------------
# Systematic finite-magma counter-model search (SEM-style). The structured
# families above only reach polynomial magmas; the irregular models that Mace4
# finds for the residual FALSE cases (carriers 4..8) need a real backtracking
# model finder. Universal instances of the hypothesis are watched on the
# still-unknown table cells that block their evaluation; when one side of an
# instance is known and the other reduces to a single unknown cell, that cell is
# forced. The negated goal is a hard disequality on a canonical witness tuple,
# and least-number symmetry breaking keeps carriers 5..8 tractable. Pure stdlib.
# ---------------------------------------------------------------------------
UNKNOWN = -1


def _mf_compile_term(term, var_positions):
    if term[0] == "var":
        return var_positions[term[1]]
    return (_mf_compile_term(term[1], var_positions),
            _mf_compile_term(term[2], var_positions))


def _mf_witness_patterns(arity, n):
    if arity == 0:
        return [()]
    out = []

    def visit(prefix, largest):
        if len(prefix) == arity:
            out.append(tuple(prefix))
            return
        upper = min(n - 1, largest + 1)
        for value in range(upper + 1):
            prefix.append(value)
            visit(prefix, max(largest, value))
            prefix.pop()

    visit([0], 0)
    out.sort(key=lambda values: (-len(set(values)), values))
    return out


def _mf_latin_flags(equation):
    """Row/column all-different constraints implied by a law `x = T` in which
    x occurs exactly once in T: for fixed other variables the map x ↦ T is the
    identity, so every step of the chain from the x-leaf to the root is a
    bijection of the (finite) carrier; a step `y ◇ u` with y a bare variable
    makes every row a permutation, a step `u ◇ y` every column. Returns
    (latin_rows, latin_cols)."""
    left, right = equation["left"], equation["right"]
    if left[0] == "var":
        var, term = left[1], right
    elif right[0] == "var":
        var, term = right[1], left
    else:
        return False, False
    if _count_var(term, var) != 1:
        return False, False
    rows = cols = False
    node = term
    while node[0] == "op":
        in_left = _count_var(node[1], var) == 1
        other = node[2] if in_left else node[1]
        if _count_var(other, var):
            return False, False
        if other[0] == "var":
            if in_left:
                cols = True
            else:
                rows = True
        node = node[1] if in_left else node[2]
    return rows, cols


def _count_var(term, var):
    if term[0] == "var":
        return 1 if term[1] == var else 0
    return _count_var(term[1], var) + _count_var(term[2], var)


class _MFSearch:
    def __init__(self, n, equation, witness_equation, witness, deadline,
                 goal_first=False):
        self.n = n
        self.size = n * n
        self.table = [UNKNOWN] * self.size
        self.deadline = deadline
        self.nodes = 0
        self.expired = False
        self.goal_first = goal_first

        eq_vars = equation["variables"]
        eq_positions = {name: i for i, name in enumerate(eq_vars)}
        self.left = _mf_compile_term(equation["left"], eq_positions)
        self.right = _mf_compile_term(equation["right"], eq_positions)

        goal_vars = witness_equation["variables"]
        goal_positions = {name: i for i, name in enumerate(goal_vars)}
        goal_left = _mf_compile_term(witness_equation["left"], goal_positions)
        goal_right = _mf_compile_term(witness_equation["right"], goal_positions)

        self.constraints = [
            (self.left, self.right, values, False)
            for values in product(range(n), repeat=len(eq_vars))
        ]
        self.constraints.append((goal_left, goal_right, witness, True))

        count = len(self.constraints)
        self.dependencies = [()] * count
        self.watchers = [set() for _ in range(self.size)]
        self.watch_trail = []
        self.assign_trail = []
        self.queue = deque(range(count))
        self.queued = bytearray(b"\x01") * count
        self.named_max = max(witness, default=-1)
        # Latin-square propagation (rows / columns all-different) when the
        # hypothesis forces it; bitmask of used values per row / column.
        self.latin_rows, self.latin_cols = _mf_latin_flags(equation)
        self.row_mask = [0] * n
        self.col_mask = [0] * n
        self.full_mask = (1 << n) - 1

    def _eval(self, term, values):
        if isinstance(term, int):
            return values[term], UNKNOWN, ()
        lv, lc, ld = self._eval(term[0], values)
        rv, rc, rd = self._eval(term[1], values)
        if lv != UNKNOWN and rv != UNKNOWN:
            cell = lv * self.n + rv
            value = self.table[cell]
            if value != UNKNOWN:
                return value, UNKNOWN, ()
            return UNKNOWN, cell, (cell,)
        deps = ld + rd
        if deps:
            deps = tuple(dict.fromkeys(deps))
        return UNKNOWN, UNKNOWN, deps

    def _set_dependencies(self, cid, new_dependencies):
        old = self.dependencies[cid]
        self.watch_trail.append((cid, old))
        for cell in old:
            self.watchers[cell].discard(cid)
        self.dependencies[cid] = new_dependencies
        for cell in new_dependencies:
            self.watchers[cell].add(cid)

    def _schedule_cell(self, cell):
        for cid in tuple(self.watchers[cell]):
            if not self.queued[cid]:
                self.queued[cid] = 1
                self.queue.append(cid)

    def _least_number_ok(self):
        used = {value for value in self.table if value != UNKNOWN}
        used.update(range(self.named_max + 1))
        if not used:
            return True
        return len(used) == max(used) + 1

    def _assign(self, cell, value):
        old = self.table[cell]
        if old != UNKNOWN:
            return old == value
        bit = 1 << value
        n = self.n
        r, c = divmod(cell, n)
        if self.latin_rows and self.row_mask[r] & bit:
            return False
        if self.latin_cols and self.col_mask[c] & bit:
            return False
        self.table[cell] = value
        self.assign_trail.append(cell)
        self.row_mask[r] |= bit
        self.col_mask[c] |= bit
        if not self._least_number_ok():
            return False
        self._schedule_cell(cell)
        # naked single: a row/column with one value missing forces its last cell
        if self.latin_rows:
            missing = self.full_mask ^ self.row_mask[r]
            if missing and (missing & (missing - 1)) == 0:
                base = r * n
                for j in range(n):
                    if self.table[base + j] == UNKNOWN:
                        if not self._assign(base + j, missing.bit_length() - 1):
                            return False
                        break
        if self.latin_cols:
            missing = self.full_mask ^ self.col_mask[c]
            if missing and (missing & (missing - 1)) == 0:
                for i in range(n):
                    if self.table[i * n + c] == UNKNOWN:
                        if not self._assign(i * n + c, missing.bit_length() - 1):
                            return False
                        break
        return True

    def _examine(self, cid):
        left, right, values, unequal = self.constraints[cid]
        lv, lc, ld = self._eval(left, values)
        rv, rc, rd = self._eval(right, values)
        if unequal:
            if lv != UNKNOWN and rv != UNKNOWN:
                self._set_dependencies(cid, ())
                return lv != rv
            if lc != UNKNOWN and rc != UNKNOWN and lc == rc:
                self._set_dependencies(cid, ())
                return False
            deps = tuple(dict.fromkeys(ld + rd))
            self._set_dependencies(cid, deps)
            return True
        if lv != UNKNOWN and rv != UNKNOWN:
            self._set_dependencies(cid, ())
            return lv == rv
        if lv != UNKNOWN and rc != UNKNOWN:
            self._set_dependencies(cid, (rc,))
            return self._assign(rc, lv)
        if rv != UNKNOWN and lc != UNKNOWN:
            self._set_dependencies(cid, (lc,))
            return self._assign(lc, rv)
        if lc != UNKNOWN and rc != UNKNOWN and lc == rc:
            self._set_dependencies(cid, ())
            return True
        deps = tuple(dict.fromkeys(ld + rd))
        self._set_dependencies(cid, deps)
        return True

    def _clear_queue(self):
        while self.queue:
            self.queued[self.queue.popleft()] = 0

    def _propagate(self):
        checks = 0
        while self.queue:
            cid = self.queue.popleft()
            self.queued[cid] = 0
            if not self._examine(cid):
                self._clear_queue()
                return False
            checks += 1
            if checks & 255 == 0 and monotonic() >= self.deadline:
                self.expired = True
                self._clear_queue()
                return False
        return True

    def _rollback(self, assign_mark, watch_mark):
        self._clear_queue()
        while len(self.watch_trail) > watch_mark:
            cid, old = self.watch_trail.pop()
            current = self.dependencies[cid]
            for cell in current:
                self.watchers[cell].discard(cid)
            self.dependencies[cid] = old
            for cell in old:
                self.watchers[cell].add(cid)
        n = self.n
        while len(self.assign_trail) > assign_mark:
            cell = self.assign_trail.pop()
            value = self.table[cell]
            self.table[cell] = UNKNOWN
            r, c = divmod(cell, n)
            self.row_mask[r] &= ~(1 << value)
            self.col_mask[c] &= ~(1 << value)

    def _choose_cell(self):
        if self.goal_first:
            goal_cells = [cell for cell in self.dependencies[-1]
                          if self.table[cell] == UNKNOWN]
            if goal_cells:
                return max(goal_cells,
                           key=lambda cell: (len(self.watchers[cell]), -cell))
        best = None
        best_score = None
        if self.latin_rows or self.latin_cols:
            # MRV under the Latin constraints: fewest values still available
            # in the cell's row/column, then most watchers.
            n = self.n
            full = self.full_mask
            for cell, value in enumerate(self.table):
                if value == UNKNOWN:
                    r, c = divmod(cell, n)
                    used = 0
                    if self.latin_rows:
                        used |= self.row_mask[r]
                    if self.latin_cols:
                        used |= self.col_mask[c]
                    avail = bin(full ^ used).count("1")
                    score = (-avail, len(self.watchers[cell]))
                    if best_score is None or score > best_score:
                        best = cell
                        best_score = score
            return best
        for cell, value in enumerate(self.table):
            if value == UNKNOWN:
                score = len(self.watchers[cell])
                if best_score is None or score > best_score:
                    best = cell
                    best_score = score
        return best

    def _dfs(self):
        self.nodes += 1
        if self.nodes & 127 == 0 and monotonic() >= self.deadline:
            self.expired = True
            return None
        cell = self._choose_cell()
        if cell is None:
            return [self.table[i:i + self.n] for i in range(0, self.size, self.n)]
        largest = self.named_max
        for prior in self.table:
            if prior > largest:
                largest = prior
        upper = min(self.n - 1, largest + 1)
        for value in range(upper + 1):
            assign_mark = len(self.assign_trail)
            watch_mark = len(self.watch_trail)
            if self._assign(cell, value) and self._propagate():
                answer = self._dfs()
                if answer is not None:
                    return answer
            self._rollback(assign_mark, watch_mark)
            if self.expired:
                return None
        return None

    def run(self):
        if not self._propagate():
            return None
        self.assign_trail.clear()
        self.watch_trail.clear()
        return self._dfs()


def find_countermodel(eq1_text, eq2_text, max_n=10, time_budget_s=8.0):
    """Smallest systematic finite countermodel as (n, table), or None."""
    try:
        equation = parse_equation(eq1_text)
        goal = parse_equation(eq2_text)
        maximum = min(10, int(max_n))
        budget = max(0.0, float(time_budget_s))
    except (TypeError, ValueError, KeyError):
        return None
    deadline = monotonic() + budget
    arity = len(goal["variables"])
    for n in range(2, min(maximum, 4) + 1):
        for witness in _mf_witness_patterns(arity, n):
            if monotonic() >= deadline:
                return None
            search = _MFSearch(n, equation, goal, witness, deadline)
            table = search.run()
            if table is not None:
                return n, table
            if search.expired:
                return None
    for n in range(5, maximum + 1):
        size_deadline = min(deadline, monotonic() + 0.75)
        for witness in _mf_witness_patterns(arity, n):
            now = monotonic()
            if now >= size_deadline:
                break
            search = _MFSearch(n, equation, goal, witness,
                               min(size_deadline, now + 0.15),
                               goal_first=(arity > 1))
            table = search.run()
            if table is not None:
                return n, table
    for n in range(5, maximum + 1):
        for witness in _mf_witness_patterns(arity, n):
            if monotonic() >= deadline:
                return None
            search = _MFSearch(n, equation, goal, witness, deadline)
            table = search.run()
            if table is not None:
                return n, table
            if search.expired:
                return None
    return None


# ---------------------------------------------------------------------------
# Extended structured false-side families on Fin n for n up to ~50.
#
# The judge's `decideFin!` is plain `decide`, and any arithmetic is allowed
# inside `submission.*` helpers, so the single-digit finOpTable limit only
# binds table certificates with n <= 10. Larger carriers are certified with
#   def submission.op (x y : Fin n) : Fin n := ⟨<expr in x.val y.val> % n, ...⟩
# (closed-form ops) or a base-n digit string packed into one Nat literal
# (explicit tables). The kernel cost is dominated by the number of hypothesis
# instances n^k (k = #variables of eq1): measured ~1 ms per instance, so the
# carrier is clamped to n^k <= FALSE_CERT_MAX_INSTANCES (~50 s of judge time).
# ---------------------------------------------------------------------------
FALSE_CERT_MAX_INSTANCES = 60000
STRUCT_MAX_N = 50


def _cert_feasible(n, eq1):
    return n ** max(1, len(eq1["variables"])) <= FALSE_CERT_MAX_INSTANCES


def _term_index_src(term):
    if term[0] == "var":
        return term[1]
    return "T[%s][%s]" % (_term_index_src(term[1]), _term_index_src(term[2]))


class _EqChecker:
    """Compiled table checks: eq holds on a full table T (list of lists)."""

    def __init__(self, eq):
        self.variables = list(eq["variables"])
        left = _term_index_src(eq["left"])
        right = _term_index_src(eq["right"])
        args = ", ".join(self.variables) if self.variables else "_unused"
        self.one = eval("lambda T, %s: %s == %s" % (args, left, right))
        loops = " ".join("for %s in R" % v for v in self.variables)
        if self.variables:
            self.all = eval("lambda T, R: all(%s == %s %s)" % (left, right, loops))
        else:
            self.all = eval("lambda T, R: %s == %s" % (left, right))

    def holds(self, table, n, probes=()):
        for pr in probes:
            if not self.one(table, *pr):
                return False
        return self.all(table, range(n))


class _PairChecker:
    """eq1 holds and eq2 fails on a table; cheap random probes first."""

    def __init__(self, eq1, eq2, seed=12345):
        self.c1 = _EqChecker(eq1)
        self.c2 = _EqChecker(eq2)
        self.k1 = len(self.c1.variables)
        self._seed = seed
        self._probe_cache = {}

    def probes(self, n, count=3):
        key = (n, count)
        got = self._probe_cache.get(key)
        if got is None:
            # deterministic pseudo-random probe assignments (LCG), no `random`
            s = self._seed + 7919 * n
            got = []
            for _ in range(count):
                vals = []
                for _j in range(self.k1):
                    s = (s * 1103515245 + 12345) & 0x7FFFFFFF
                    vals.append((s >> 8) % n)
                got.append(tuple(vals))
            self._probe_cache[key] = got
        return got

    def test(self, table, n):
        if not self.c1.holds(table, n, self.probes(n)):
            return False
        return not self.c2.all(table, range(n))


def _lean_affine_expr(n, a, b, c=0):
    parts = []
    if a:
        parts.append("%d * x.val" % a)
    if b:
        parts.append("%d * y.val" % b)
    if c:
        parts.append("%d" % c)
    if not parts:
        parts.append("0")
    return "(%s) %% %d" % (" + ".join(parts), n)


def _witness(stage, n, table=None, lean_op=None, extra=None):
    out = {"stage": stage, "n": n}
    if table is not None:
        out["table"] = table
    if lean_op is not None:
        out["lean_op"] = lean_op
    if extra:
        out.update(extra)
    return out


def linear_mod_n_counterexample(eq1, eq2, deadline, n_lo=2, n_hi=STRUCT_MAX_N):
    # x ◇ y = a x + b y (mod n), all n (composite too); exact symbolic check:
    # the coefficient vector of each side is a linear form over Z_n and the law
    # holds iff all coefficient differences vanish mod n.
    for n in range(n_lo, n_hi + 1):
        if not _cert_feasible(n, eq1):
            return None
        if monotonic() >= deadline:
            return None
        for a in range(n):
            for b in range(n):
                if linear_equation_holds(eq1, n, a, b) and linear_equation_fails(eq2, n, a, b):
                    table = linear_table(n, a, b) if n <= 10 else None
                    return _witness("linear_n", n, table, _lean_affine_expr(n, a, b),
                                    {"a": a, "b": b})
    return None


def affine_mod_n_counterexample(eq1, eq2, deadline, n_lo=2, n_hi=STRUCT_MAX_N):
    # x ◇ y = a x + b y + c (mod n). The linear part must already make eq1 hold
    # coefficient-wise, which prunes (a, b) before the constant loop.
    for n in range(n_lo, n_hi + 1):
        if not _cert_feasible(n, eq1):
            return None
        if monotonic() >= deadline:
            return None
        for a in range(n):
            for b in range(n):
                if not linear_equation_holds(eq1, n, a, b):
                    continue
                for c in range(1, n):
                    if affine_equation_holds(eq1, n, a, b, c) and affine_equation_fails(eq2, n, a, b, c):
                        table = affine_table(n, a, b, c) if n <= 10 else None
                        return _witness("affine_n", n, table, _lean_affine_expr(n, a, b, c),
                                        {"a": a, "b": b, "c": c})
    return None


def _vec_space(p, k):
    # elements of F_p^k encoded as ints 0..p^k-1 (digit i = coordinate i);
    # returns (n, add_table, matrices) where matrices are the lists Ax for
    # every k x k matrix A over F_p, as images of all vectors.
    n = p ** k
    digits = [[(v // p ** i) % p for i in range(k)] for v in range(n)]
    add = [[0] * n for _ in range(n)]
    for u in range(n):
        du = digits[u]
        for v in range(n):
            dv = digits[v]
            add[u][v] = sum(((du[i] + dv[i]) % p) * p ** i for i in range(k))
    images = []
    for enc in range(p ** (k * k)):
        rows = [[(enc // p ** (k * i + j)) % p for j in range(k)] for i in range(k)]
        img = []
        for v in range(n):
            dv = digits[v]
            w = 0
            for i in range(k):
                s = 0
                for j in range(k):
                    s += rows[i][j] * dv[j]
                w += (s % p) * p ** i
            img.append(w)
        images.append(img)
    return n, add, images


_VEC_SPACE_CACHE = {}


def vector_linear_counterexample(eq1, eq2, p, k, deadline, checker=None, use_affine=True):
    # x ◇ y = A x + B y (+ c) over F_p^k (matrix-linear magmas; F_2^2 is the
    # frozen solver's f2_matrix family, this generalizes to F_2^3, F_3^2, ...).
    n = p ** k
    if not _cert_feasible(n, eq1):
        return None
    key = (p, k)
    if key not in _VEC_SPACE_CACHE:
        _VEC_SPACE_CACHE[key] = _vec_space(p, k)
    n, add, images = _VEC_SPACE_CACHE[key]
    if checker is None:
        checker = _PairChecker(eq1, eq2)
    rng = range(n)
    consts = range(n) if use_affine else (0,)
    for ai, ax in enumerate(images):
        if monotonic() >= deadline:
            return None
        rows_a = [add[ax[i]] for i in rng]
        for bi, bx in enumerate(images):
            table = [[rows_a[i][bx[j]] for j in rng] for i in rng]
            if not checker.c1.holds(table, n, checker.probes(n)):
                # the linear part fixes eq1's coefficient identities; no
                # constant can rescue it.
                continue
            if not checker.c2.all(table, rng):
                return _witness("vec_linear_%d_%d" % (p, k), n, table, None,
                                {"a_idx": ai, "b_idx": bi, "c": 0})
            if use_affine:
                for c in range(1, n):
                    table = [[add[rows_a[i][bx[j]]][c] for j in rng] for i in rng]
                    if checker.test(table, n):
                        return _witness("vec_affine_%d_%d" % (p, k), n, table, None,
                                        {"a_idx": ai, "b_idx": bi, "c": c})
    return None


_POLY_MONOMIALS = (
    # (deg_x, deg_y)
    (0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (0, 2), (2, 1), (1, 2), (3, 0), (0, 3),
)


def _poly_table(n, coeffs):
    # coeffs aligned with _POLY_MONOMIALS
    table = []
    for i in range(n):
        row = []
        for j in range(n):
            s = 0
            for (dx, dy), c in zip(_POLY_MONOMIALS, coeffs):
                if c:
                    s += c * pow(i, dx, n) * pow(j, dy, n)
            row.append(s % n)
        table.append(row)
    return table


def _poly_lean_expr(n, coeffs):
    parts = []
    for (dx, dy), c in zip(_POLY_MONOMIALS, coeffs):
        if not c:
            continue
        factors = []
        if c != 1 or (dx == 0 and dy == 0):
            factors.append(str(c))
        factors.extend(["x.val"] * dx)
        factors.extend(["y.val"] * dy)
        parts.append(" * ".join(factors))
    if not parts:
        parts.append("0")
    return "(%s) %% %d" % (" + ".join(parts), n)


def poly_sample_counterexample(eq1, eq2, deadline, n_lo=2, n_hi=16, checker=None,
                               per_n_share=None):
    # FinitePoly-style: x ◇ y = sum c_ij x^i y^j (mod n) with monomials up to
    # degree 3, sampled deterministically (LCG) per carrier size within the
    # deadline; the exhaustive degree<=2 grid for n <= 6 already ran earlier.
    if checker is None:
        checker = _PairChecker(eq1, eq2)
    sizes = [n for n in range(n_lo, n_hi + 1) if _cert_feasible(n, eq1)]
    if not sizes:
        return None
    seed = 987654321
    m = len(_POLY_MONOMIALS)
    while monotonic() < deadline:
        for n in sizes:
            slice_end = min(deadline, monotonic() + (per_n_share or 0.4))
            while monotonic() < slice_end:
                coeffs = []
                for _ in range(m):
                    seed = (seed * 6364136223846793005 + 1442695040888963407) & 0xFFFFFFFFFFFFFFFF
                    coeffs.append((seed >> 33) % n)
                # sparsify: zero out a random subset so low-degree forms dominate
                seed = (seed * 6364136223846793005 + 1442695040888963407) & 0xFFFFFFFFFFFFFFFF
                mask = (seed >> 33) % (1 << m)
                coeffs = [c if (mask >> i) & 1 else 0 for i, c in enumerate(coeffs)]
                if not any(coeffs[1:]):
                    continue
                table = _poly_table(n, coeffs)
                if checker.test(table, n):
                    return _witness("poly_sample", n, table if n <= 10 else None,
                                    _poly_lean_expr(n, coeffs), {"coeffs": coeffs})
        if monotonic() >= deadline:
            break
    return None


def poly_quadratic_grid_counterexample(eq1, eq2, deadline, n_lo=7, n_hi=10, checker=None):
    # exhaustive degree<=2 grid c0 + a x + b y + d xy + e x^2 + f y^2 for the
    # sizes the frozen quadratic stage does not reach (n_lo..n_hi), deadline-bounded.
    if checker is None:
        checker = _PairChecker(eq1, eq2)
    for n in range(n_lo, n_hi + 1):
        if not _cert_feasible(n, eq1):
            return None
        rng = range(n)
        for a in rng:
            for b in rng:
                for d in rng:
                    if monotonic() >= deadline:
                        return None
                    for e in rng:
                        for f in rng:
                            for c0 in rng:
                                coeffs = (c0, a, b, d, e, f, 0, 0, 0, 0)
                                table = _poly_table(n, coeffs)
                                if checker.test(table, n):
                                    return _witness("poly_quadratic_grid", n, table, None,
                                                    {"coeffs": coeffs})
    return None


def structured_counterexample(eq1, eq2, deadline, deep=False):
    """Extended structured families (cheap, exact). deep=True adds the heavier
    sampled/grid families bounded by the deadline."""
    found = linear_mod_n_counterexample(eq1, eq2, deadline, 2, STRUCT_MAX_N)
    if found is not None:
        return found
    found = affine_mod_n_counterexample(eq1, eq2, deadline, 2, STRUCT_MAX_N)
    if found is not None:
        return found
    checker = _PairChecker(eq1, eq2)
    found = vector_linear_counterexample(eq1, eq2, 3, 2, deadline, checker)
    if found is not None:
        return found
    found = vector_linear_counterexample(eq1, eq2, 2, 3, deadline, checker)
    if found is not None:
        return found
    if not deep:
        return None
    found = poly_quadratic_grid_counterexample(eq1, eq2, min(deadline, monotonic() + 20.0), 7, 8, checker)
    if found is not None:
        return found
    found = vector_linear_counterexample(eq1, eq2, 5, 2, min(deadline, monotonic() + 20.0), checker,
                                         use_affine=False)
    if found is not None:
        return found
    found = poly_sample_counterexample(eq1, eq2, min(deadline, monotonic() + 20.0), 2, 16, checker)
    if found is not None:
        return found
    return None


# ---------------------------------------------------------------------------
# Austin pairs (finite-true, general-false) need an infinite countermodel. A
# canned ℕ-carrier model: the ETP 1659-model f (parity-patched successor op)
# satisfies laws 1659 and 2473 (the latter via the replayed implication
# 1659 ⇒ 2473); its opposite magma (x ◇ y := f y x) satisfies their duals
# (2000 and 1167). If the hypothesis is one of these laws up to variable
# renaming and the goal fails on the model at small naturals, the certificate
# proves the hypothesis by the canned lemma and refutes the goal by `decide`
# on the closed witness instance. Extending the table = adding (op, law,
# lemma, lemma-args, proof text) rows.
# ---------------------------------------------------------------------------
_AUSTIN_F_LEMMAS = """\
theorem mod_two_succ_0_1_from (n : ℕ) : n % 2 = 0 → (n + 1) % 2 = 1 := by omega
theorem mod_two_succ_1_0_from (n : ℕ) : n % 2 = 1 → (n + 1) % 2 = 0 := by omega
theorem mod_two_pred_0_1_to (n : ℕ) : (n + 1) % 2 = 0 → n % 2 = 1 := by omega
theorem mod_two_pred_1_0_to (n : ℕ) : (n + 1) % 2 = 1 → n % 2 = 0 := by omega
theorem mod_two_ne_down_to (n m : ℕ) : (n + 1) % 2 = m % 2 → ¬ n % 2 = m % 2 := by omega
theorem mod_two_eq_down_to (n m : ℕ) : (n + 1) % 2 ≠ m % 2 → n % 2 = m % 2 := by omega
theorem mod_two_ne_up_from (n m : ℕ) : n % 2 = m % 2 → ¬ (n + 1) % 2 = m % 2 := by omega
theorem mod_two_eq_up_from (n m : ℕ) : n % 2 ≠ m % 2 → (n + 1) % 2 = m % 2 := by omega

def f (x : ℕ) (y : ℕ) : ℕ :=
  match x with
  | 0 =>
    if y % 2 = 0
    then 1 else 0
  | n + 1 =>
    if x % 2 = y % 2
    then n + 2 else n

theorem f_1659 :
  ∀ (x y z : ℕ),
  x = f (f x y) (f (f y y) z ) := by
  intro xo yo z
  by_cases z_cong_0 : z % 2 = 0
  · match xo, yo with
    | 0, 0 =>
      simp [f]
      split
      · simp
      · simp
    | 0, y+1 =>
      simp [f]
      by_cases y1_cong_0 : (y + 1) % 2 = 0
      · have y_cong_1 : y % 2  = 1 :=
          mod_two_pred_0_1_to y y1_cong_0
        simp [y1_cong_0,y_cong_1,z_cong_0]
      · have y1_cong_1 : (y + 1) % 2 = 1 :=
            Nat.mod_two_ne_zero.mp y1_cong_0
        have y_cong_0 : y % 2 = 0 :=
          mod_two_pred_1_0_to y y1_cong_1
        simp [y1_cong_0,y_cong_0,z_cong_0]
    | x+1, 0 =>
      simp [f]
      by_cases x1_cong_0 : (x + 1) % 2 = 0
      · have x_cong_1 : x % 2  = 1 :=
          mod_two_pred_0_1_to x x1_cong_0
        simp [x1_cong_0,x_cong_1,z_cong_0]
      · have x1_cong_1 : (x + 1) % 2 = 1 :=
            Nat.mod_two_ne_zero.mp x1_cong_0
        have x_cong_0 : x % 2 = 0 :=
          mod_two_pred_1_0_to x x1_cong_1
        simp [x1_cong_0,x_cong_0,z_cong_0]
        split
        simp_all only [zero_add, one_ne_zero, not_false_eq_true, Nat.mod_succ, Nat.zero_mod]
        simp
    | x+1, y+1 =>
      by_cases y1_cong_0 : (y + 1) % 2 = 0
      · have y_cong_1 : y % 2  = 1 :=
          mod_two_pred_0_1_to y y1_cong_0
        by_cases x1_cong_0 : (x + 1) % 2 = 0
        · have x_cong_1 : x % 2  = 1 :=
            mod_two_pred_0_1_to x x1_cong_0
          simp [f,y1_cong_0,y_cong_1,x1_cong_0,x_cong_1,z_cong_0]
        · have x1_cong_1 : (x + 1) % 2 = 1 :=
            Nat.mod_two_ne_zero.mp x1_cong_0
          have x_cong_0 : x % 2  = 0 :=
            mod_two_pred_1_0_to x x1_cong_1
          simp [f,y1_cong_0,y_cong_1,x1_cong_0,x_cong_0,z_cong_0]
          split
          simp
          simp
      · have y1_cong_1 : (y + 1) % 2 = 1 :=
          Nat.mod_two_ne_zero.mp y1_cong_0
        have y_cong_0 : y % 2 = 0 :=
          mod_two_pred_1_0_to y y1_cong_1
        by_cases x1_cong_0 : (x + 1) % 2 = 0
        · have x_cong_1 : x % 2  = 1 :=
            mod_two_pred_0_1_to x x1_cong_0
          simp [f,x1_cong_0,y1_cong_1,y_cong_0,z_cong_0,x_cong_1]
          split
          simp_all only [one_ne_zero, not_false_eq_true, zero_add, Nat.mod_succ]
          simp
        · have x1_cong_1 : (x + 1) % 2 = 1 :=
            Nat.mod_two_ne_zero.mp x1_cong_0
          have x_cong_0 : x % 2  = 0 :=
            mod_two_pred_1_0_to x x1_cong_1
          simp [f,y_cong_0,x1_cong_1,y1_cong_1,x_cong_0,z_cong_0]
  · have z_cong_1 : z % 2 = 1 :=
      Nat.mod_two_ne_zero.mp z_cong_0
    match xo, yo with
    | 0, 0 =>
      simp [f]
      split
      · simp
      · simp
    | 0, y+1 =>
      simp [f]
      by_cases y1_cong_0 : (y + 1) % 2 = 0
      · have y_cong_1 : y % 2  = 1 :=
          mod_two_pred_0_1_to y y1_cong_0
        simp [y1_cong_0,y_cong_1,z_cong_1]
      · have y1_cong_1 : (y + 1) % 2 = 1 :=
            Nat.mod_two_ne_zero.mp y1_cong_0
        have y_cong_0 : y % 2 = 0 :=
          mod_two_pred_1_0_to y y1_cong_1
        simp [y1_cong_0,y_cong_0,z_cong_1]
    | x+1, 0 =>
      simp [f]
      by_cases x1_cong_0 : (x + 1) % 2 = 0
      · have x_cong_1 : x % 2  = 1 :=
          mod_two_pred_0_1_to x x1_cong_0
        simp [x1_cong_0,x_cong_1,z_cong_1]
      · have x1_cong_1 : (x + 1) % 2 = 1 :=
            Nat.mod_two_ne_zero.mp x1_cong_0
        have x_cong_0 : x % 2 = 0 :=
          mod_two_pred_1_0_to x x1_cong_1
        simp [x1_cong_0,x_cong_0,z_cong_1]
        split
        simp_all only [zero_add, one_ne_zero, not_false_eq_true, Nat.mod_succ, Nat.zero_mod]
        simp
    | x+1, y+1 =>
      by_cases y1_cong_0 : (y + 1) % 2 = 0
      · have y_cong_1 : y % 2  = 1 :=
          mod_two_pred_0_1_to y y1_cong_0
        by_cases x1_cong_0 : (x + 1) % 2 = 0
        · have x_cong_1 : x % 2  = 1 :=
            mod_two_pred_0_1_to x x1_cong_0
          simp [f,y1_cong_0,y_cong_1,x1_cong_0,x_cong_1,z_cong_1]
        · have x1_cong_1 : (x + 1) % 2 = 1 :=
            Nat.mod_two_ne_zero.mp x1_cong_0
          have x_cong_0 : x % 2  = 0 :=
            mod_two_pred_1_0_to x x1_cong_1
          simp [f,y1_cong_0,y_cong_1,x1_cong_0,x_cong_0,z_cong_1]
          split
          simp
          simp
      · have y1_cong_1 : (y + 1) % 2 = 1 :=
          Nat.mod_two_ne_zero.mp y1_cong_0
        have y_cong_0 : y % 2 = 0 :=
          mod_two_pred_1_0_to y y1_cong_1
        by_cases x1_cong_0 : (x + 1) % 2 = 0
        · have x_cong_1 : x % 2  = 1 :=
            mod_two_pred_0_1_to x x1_cong_0
          simp [f,x1_cong_0,y1_cong_1,y_cong_0,z_cong_1,x_cong_1]
          split
          simp_all only [one_ne_zero, not_false_eq_true, zero_add, Nat.mod_succ]
          simp
        · have x1_cong_1 : (x + 1) % 2 = 1 :=
            Nat.mod_two_ne_zero.mp x1_cong_0
          have x_cong_0 : x % 2  = 0 :=
            mod_two_pred_1_0_to x x1_cong_1
          simp [f,y_cong_0,x1_cong_1,y1_cong_1,x_cong_0,z_cong_1]
"""

_AUSTIN_F_IMPL = """\
theorem impl (G : Type) [Magma G] (h : ∀ x y z : G, x = (x ◇ y) ◇ ((y ◇ y) ◇ z)) :
    ∀ x y z : G, x = (x ◇ ((y ◇ y) ◇ z)) ◇ y := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) = X0 := by first | exact (h _ _ _).symm | exact h _ _ _ | exact (h _ _).symm | exact h _ _ | exact (h _ _ _ _).symm | exact h _ _ _ _
  have eq10 : sK0 ≠ ((sK0 ◇ ((sK1 ◇ sK1) ◇ sK2)) ◇ sK1) := by first | exact nh | exact Ne.symm nh
  have eq13 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X2 := by have hb := eq9 X2 X0 ((X0 ◇ X0) ◇ X2); have ha := eq9 X0 X0 X2; first | (rw [ha] at hb; first | exact hb | exact hb.symm | exact Ne.symm hb) | (rw [← ha] at hb; first | exact hb | exact hb.symm | exact Ne.symm hb) | grind
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by have hb := eq13 ((X1 ◇ X1) ◇ X2) (X0 ◇ X1); have ha := eq9 X0 X1 X2; first | (rw [ha] at hb; first | exact hb | exact hb.symm | exact Ne.symm hb) | (rw [← ha] at hb; first | exact hb | exact hb.symm | exact Ne.symm hb) | grind
  have eq19 : sK0 ≠ ((sK0 ◇ sK1) ◇ sK1) := by have hb := eq10; have ha := eq15 sK0 sK1 sK2; first | (rw [← ha] at hb; first | exact hb | exact hb.symm | exact Ne.symm hb) | (rw [ha] at hb; first | exact hb | exact hb.symm | exact Ne.symm hb) | grind
  first | exact eq19 (eq13 ..) | exact eq19 (eq13 ..).symm | exact eq19 rfl | grind

theorem f_2473 : ∀ x y z : ℕ, x = f (f x (f (f y y) z)) y :=
  @impl ℕ ⟨f⟩ f_1659
"""


def _austin_f(x, y):
    if x == 0:
        return 1 if y % 2 == 0 else 0
    n = x - 1
    return n + 2 if x % 2 == y % 2 else n


def _austin_f_dual(x, y):
    return _austin_f(y, x)


# (op_key, law text, lemma, lemma argument variables, needs_impl)
_AUSTIN_LAWS = (
    ("f", "x = (x ◇ y) ◇ ((y ◇ y) ◇ z)", "f_1659", ("x", "y", "z"), False),
    ("f", "x = (x ◇ ((y ◇ y) ◇ z)) ◇ y", "f_2473", ("x", "y", "z"), True),
    ("fdual", "x = (z ◇ (y ◇ y)) ◇ (y ◇ x)", "f_1659", ("x", "y", "z"), False),
    ("fdual", "x = y ◇ ((z ◇ (y ◇ y)) ◇ x)", "f_2473", ("x", "y", "z"), True),
)
_AUSTIN_OPS = {
    "f": ("fun x y => submission.f x y", _austin_f),
    "fdual": ("fun x y => submission.f y x", _austin_f_dual),
}


def _match_renaming(pattern, subject, sigma):
    # structural equality up to an injective variable renaming pattern -> subject
    if pattern[0] == "var":
        if subject[0] != "var":
            return False
        got = sigma.get(pattern[1])
        if got is None:
            if subject[1] in sigma.values():
                return False
            sigma[pattern[1]] = subject[1]
            return True
        return got == subject[1]
    if subject[0] != "op":
        return False
    return (_match_renaming(pattern[1], subject[1], sigma)
            and _match_renaming(pattern[2], subject[2], sigma))


def austin_counterexample(eq1_text, eq2_text, max_value=6):
    try:
        eq1 = parse_equation(eq1_text)
        eq2 = parse_equation(eq2_text)
    except ParseError:
        return None
    for op_key, law_text, lemma, lemma_args, needs_impl in _AUSTIN_LAWS:
        law = parse_equation(law_text)
        sigma = {}
        if not (_match_renaming(law["left"], eq1["left"], sigma)
                and _match_renaming(law["right"], eq1["right"], sigma)):
            continue
        if set(sigma.values()) != set(eq1["variables"]):
            continue
        lean_op, py_op = _AUSTIN_OPS[op_key]
        witness = None
        vals = range(max_value)
        for assignment in product(vals, repeat=len(eq2["variables"])):
            env = dict(zip(eq2["variables"], assignment))
            if eval_term(eq2["left"], env, py_op) != eval_term(eq2["right"], env, py_op):
                witness = assignment
                break
        if witness is None:
            continue
        args = " ".join(sigma[v] for v in lemma_args)
        code = (
            "import JudgeProblem\n"
            "import Mathlib.Tactic\n\n"
            "namespace submission\n"
            + _AUSTIN_F_LEMMAS + "\n"
            + (_AUSTIN_F_IMPL + "\n" if needs_impl else "")
            + "end submission\n\n"
            "def submission : Goal := by\n"
            "  refine ⟨ℕ, ⟨%s⟩, ?_, ?_⟩\n"
            "  · intro %s\n"
            "    exact submission.%s %s\n"
            "  · intro h\n"
            "    exact absurd (h %s) (by decide)\n"
            % (lean_op, " ".join(eq1["variables"]), lemma, args,
               " ".join(str(v) for v in witness))
        )
        return {"stage": "austin_nat", "n": 0, "carrier": "nat", "code": code,
                "law": law_text, "witness": list(witness)}
    return None


# affine stage disabled by default: empirically +0 on normal+hard1/2/3 samples
# (with no constants in the input language, nonzero affine offsets are
# equationally equivalent to linear), and it costs up to AFFINE_CANDIDATE_LIMIT
# evals/problem. Kept for reference; flip use_affine=True to re-enable.
def search_counterexample(eq1_text, eq2_text, use_linear=True, use_affine=False,
                          use_model_finder=True, model_finder_budget_s=8.0,
                          use_structured=True, structured_budget_s=6.0,
                          use_deep=False, deep_budget_s=60.0, use_austin=True):
    eq1 = parse_equation(eq1_text)
    eq2 = parse_equation(eq2_text)
    if use_linear:
        found = brute_counterexample(eq1, eq2, max_n=3)
        if found is not None:
            return found
        found = linear_counterexample(eq1, eq2)
        if found is not None:
            return found
        found = f2_matrix_counterexample(eq1, eq2)
        if found is not None:
            return found
        # structured Z_n families (composite-n linear, affine, quadratic) that the
        # prime-only linear and F2^2 stages above cannot reach.
        found = polynomial_counterexample(eq1, eq2)
        if found is not None:
            return found
        if use_affine:
            found = affine_counterexample(eq1, eq2)
            if found is not None:
                return found
    if use_structured:
        # Fin-n arithmetic families beyond the finOpTable cap (n <= 50 linear /
        # affine, F_3^2 and F_2^3 matrix-linear); certified via submission.op.
        found = structured_counterexample(eq1, eq2, monotonic() + structured_budget_s,
                                          deep=False)
        if found is not None:
            return found
    if use_austin:
        found = austin_counterexample(eq1_text, eq2_text)
        if found is not None:
            return found
    if use_deep:
        found = structured_counterexample(eq1, eq2, monotonic() + deep_budget_s,
                                          deep=True)
        if found is not None:
            return found
    # Last resort: systematic SEM-style finite-model search for the irregular
    # carriers 4..8 that the structured families miss. Most expensive stage, so
    # it runs only after everything cheaper has failed (and is deferred past the
    # cheap true-proof stages by the caller — see main()).
    if use_model_finder:
        mf = find_countermodel(eq1_text, eq2_text, max_n=10,
                               time_budget_s=model_finder_budget_s)
        if mf is not None:
            n, table = mf
            return {"stage": "model_finder", "n": n, "table": table}
    return None


def _big_table_nat(n, table):
    # pack the Cayley table as one base-n digit string: digit (i*n + j) = i ◇ j
    total = 0
    weight = 1
    for i in range(n):
        for j in range(n):
            total += table[i][j] * weight
            weight *= n
    return total


def make_false_code_arith(n, lean_op=None, table=None):
    # Fin-n certificate via an arithmetic `submission.op` (any n; used for
    # n >= 11 where finOpTable's single-digit parser cannot be used). Either a
    # closed-form expression in x.val / y.val (already reduced `% n`) or an
    # explicit table packed into a Nat literal and read back with `/ n^k % n`
    # (kernel Nat arithmetic is GMP-accelerated, so lookups are O(1)).
    if lean_op is None:
        body = (
            "def tbl : Nat := %d\n"
            "def op (x y : Fin %d) : Fin %d := ⟨(tbl / %d ^ (x.val * %d + y.val)) %% %d, "
            "Nat.mod_lt _ (by decide)⟩\n" % (_big_table_nat(n, table), n, n, n, n, n)
        )
    else:
        body = (
            "def op (x y : Fin %d) : Fin %d := ⟨%s, Nat.mod_lt _ (by decide)⟩\n"
            % (n, n, lean_op)
        )
    return (
        "import JudgeProblem\n"
        "import JudgeDecide.DecideBang\n\n"
        "namespace submission\n"
        + body +
        "end submission\n\n"
        "set_option maxRecDepth 1000000 in\n"
        "set_option maxHeartbeats 1000000 in\n"
        "def submission : Goal := by\n"
        "  let m : Magma (Fin %d) := { op := submission.op }\n"
        "  refine \u27e8Fin %d, m, ?_\u27e9\n"
        "  decideFin!\n" % (n, n)
    )


def make_false_code(problem, cex):
    n = cex["n"]
    if cex.get("carrier") == "nat":
        return cex["code"]
    if n > 10:
        # beyond finOpTable's single-digit parser: arithmetic submission.op
        return make_false_code_arith(n, cex.get("lean_op"), cex.get("table"))
    if "a" in cex and "b" in cex:
        a, b = cex["a"], cex["b"]
        if "c" in cex:
            table = affine_table(n, a, b, cex["c"])
        else:
            table = linear_table(n, a, b)
        cex = dict(cex)
        cex["table"] = table

    # False certificates must stay within the official declaration whitelist.
    # Linear, affine, brute, and Fin4 matrix witnesses use finOpTable.
    head = (
        "import JudgeProblem\n"
        "import JudgeDecide.DecideBang\n"
        "import JudgeFinOp.MemoFinOp\n"
        "open MemoFinOp\n\n"
        # larger carriers overflow decideFin!'s default recursion / heartbeat budget;
        # lift both within the 300s lean_timeout.
        "set_option maxRecDepth 1000000 in\n"
        "set_option maxHeartbeats 1000000 in\n"
        "def submission : Goal := by\n"
    )
    tail = (
        f"  refine \u27e8Fin {n}, m, ?_\u27e9\n"
        f"  decideFin!\n"
    )
    if "a_mat" in cex and "b_mat" in cex:
        a, b = cex["a_mat"], cex["b_mat"]
        c = cex.get("c_vec", (0, 0))
        table = []
        for i in range(4):
            row = []
            for j in range(4):
                lo = (
                    a[0][0] * (i % 2)
                    + a[0][1] * ((i // 2) % 2)
                    + b[0][0] * (j % 2)
                    + b[0][1] * ((j // 2) % 2)
                    + c[0]
                )
                hi = (
                    a[1][0] * (i % 2)
                    + a[1][1] * ((i // 2) % 2)
                    + b[1][0] * (j % 2)
                    + b[1][1] * ((j // 2) % 2)
                    + c[1]
                )
                row.append(((lo % 2) + 2 * (hi % 2)) % 4)
            table.append(row)
        cex = dict(cex)
        cex["table"] = table
    table_str = json.dumps(cex["table"])
    op = (
        f"  let m : Magma (Fin {n}) := {{\n"
        f"    op := finOpTable \"{table_str}\"\n"
        f"  }}\n"
    )
    return head + op + tail


def make_true_code(problem, proof_body):
    lines = proof_body.strip().split("\n")
    indented = "\n".join("  " + l if l.strip() else "" for l in lines)
    return (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        f"{indented}\n"
    )


def _distinct_vars(text):
    out, seen = [], set()
    for v in re.findall(r"\b([a-z])\b", text):
        if v not in seen:
            seen.add(v)
            out.append(v)
    return out


def singleton_true_proof(eq1_text, eq2_text):
    # No-LLM proof for true implications whose hypothesis E1 has the form
    # `x = <term not containing x>`: such a law forces the magma to be a singleton
    # (all elements equal), so any E2 follows. Mirrors the official baseline's
    # singleton stage. Returns a proof body string, or None if E1 isn't this shape.
    parts = eq1_text.split("=", 1)
    if len(parts) != 2 or parts[0].strip() != "x":
        return None
    if "x" in set(re.findall(r"\b([a-z])\b", parts[1])):
        return None
    eq1_vars = _distinct_vars(eq1_text)
    eq2_vars = _distinct_vars(eq2_text)
    rhs_lhs, rhs_rhs = eq2_text.split("=", 1)
    filler = " ".join(["a"] * (len(eq1_vars) - 1))
    return (
        f"intro {' '.join(eq2_vars)}\n"
        f"have singleton : ∀ (a b : G), a = b := "
        f"fun a b => (h a {filler}).trans (h b {filler}).symm\n"
        f"exact singleton ({rhs_lhs.strip()}) ({rhs_rhs.strip()})"
    )


def _term_to_lean(term):
    if term[0] == "var":
        return term[1]
    return f"({_term_to_lean(term[1])} ◇ {_term_to_lean(term[2])})"


def _match_term(pattern, subject, subst):
    if pattern[0] == "var":
        var = pattern[1]
        if var in subst:
            return subst[var] == subject
        subst[var] = subject
        return True
    if pattern[0] == "op" and subject[0] == "op":
        return _match_term(pattern[1], subject[1], subst) and _match_term(pattern[2], subject[2], subst)
    return False


def _apply_subst(term, subst):
    if term[0] == "var":
        return subst.get(term[1], term)
    return ("op", _apply_subst(term[1], subst), _apply_subst(term[2], subst))


def _count_occurrences(term, needle):
    count = 1 if term == needle else 0
    if term[0] == "op":
        count += _count_occurrences(term[1], needle)
        count += _count_occurrences(term[2], needle)
    return count


def _subst_args(eq1_vars, subst):
    if any(var not in subst for var in eq1_vars):
        return None
    return [_term_to_lean(subst[var]) for var in eq1_vars]


def _proof_lines(eq2_vars, tactic_line):
    lines = []
    if eq2_vars:
        lines.append(f"intro {' '.join(eq2_vars)}")
    lines.append(tactic_line)
    return "\n".join(lines)


def _h_application(args):
    if args:
        return f"h {' '.join(args)}"
    return "h"


def substitution_instance_true_proof(eq1_text, eq2_text):
    try:
        eq1 = parse_equation(eq1_text)
        eq2 = parse_equation(eq2_text)
    except ParseError:
        return None

    eq1_vars = _distinct_vars(eq1_text)
    eq2_vars = _distinct_vars(eq2_text)

    subst = {}
    if _match_term(eq1["left"], eq2["left"], subst) and _match_term(eq1["right"], eq2["right"], subst):
        args = _subst_args(eq1_vars, subst)
        if args is not None:
            return _proof_lines(eq2_vars, f"exact {_h_application(args)}")

    subst = {}
    if _match_term(eq1["right"], eq2["left"], subst) and _match_term(eq1["left"], eq2["right"], subst):
        args = _subst_args(eq1_vars, subst)
        if args is not None:
            return _proof_lines(eq2_vars, f"exact ({_h_application(args)}).symm")

    return None



# ---------------------------------------------------------------------------
# Singleton-forced TRUE prover (proof-producing superposition). For a
# hypothesis that forces the magma to be trivial, a bounded given-clause
# superposition search derives a collapse identity (one side a fresh
# variable); its derivation DAG is replayed as Lean `have` lemmas
# (h-instances + congrArg/.symm/.trans), then a uniform singleton lemma
# closes the goal. Pure stdlib, deterministic, judge-verified.
# ---------------------------------------------------------------------------
class _SPParseError(ValueError):
    pass


class _SPParser:
    def __init__(self, source):
        self.tokens = re.findall(r"[a-z]|[()=]|◇", source)
        compact = re.sub(r"\s+", "", source)
        if "".join(self.tokens) != compact:
            raise _SPParseError("invalid equation")
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def take(self, expected=None):
        token = self.peek()
        if token is None or (expected is not None and token != expected):
            raise _SPParseError("unexpected token")
        self.pos += 1
        return token

    def atom(self):
        if self.peek() == "(":
            self.take("(")
            result = self.expr()
            self.take(")")
            return result
        token = self.take()
        if not (len(token) == 1 and token.islower()):
            raise _SPParseError("expected variable")
        return ("v", token)

    def expr(self):
        result = self.atom()
        while self.peek() == "◇":
            self.take()
            result = ("o", result, self.atom())
        return result

    def equation(self):
        left = self.expr()
        self.take("=")
        right = self.expr()
        if self.peek() is not None:
            raise _SPParseError("trailing input")
        return left, right


def _size(term):
    return 1 if term[0] == "v" else 1 + _size(term[1]) + _size(term[2])


def _vars(term, out=None):
    if out is None:
        out = set()
    if term[0] == "v":
        out.add(term[1])
    else:
        _vars(term[1], out)
        _vars(term[2], out)
    return out


def _subst(term, substitution):
    while term[0] == "v" and term[1] in substitution:
        replacement = substitution[term[1]]
        if replacement == term:
            break
        term = replacement
    if term[0] == "v":
        return term
    return ("o", _subst(term[1], substitution), _subst(term[2], substitution))


def _occurs(variable, term, substitution):
    term = _subst(term, substitution)
    if term[0] == "v":
        return term[1] == variable
    return (_occurs(variable, term[1], substitution)
            or _occurs(variable, term[2], substitution))


def _unify(left, right):
    substitution = {}
    pending = [(left, right)]
    while pending:
        a, b = pending.pop()
        a, b = _subst(a, substitution), _subst(b, substitution)
        if a == b:
            continue
        if a[0] == "v":
            if _occurs(a[1], b, substitution):
                return None
            substitution[a[1]] = b
        elif b[0] == "v":
            if _occurs(b[1], a, substitution):
                return None
            substitution[b[1]] = a
        elif a[0] == "o" and b[0] == "o":
            pending.append((a[1], b[1]))
            pending.append((a[2], b[2]))
        else:
            return None
    return {name: _subst(value, substitution)
            for name, value in substitution.items()}


def _positions(term, path=()):
    """All non-variable positions, root first."""
    if term[0] != "o":
        return
    yield path, term
    yield from _positions(term[1], path + (1,))
    yield from _positions(term[2], path + (2,))


def _replace(term, path, replacement):
    if not path:
        return replacement
    if path[0] == 1:
        return ("o", _replace(term[1], path[1:], replacement), term[2])
    return ("o", term[1], _replace(term[2], path[1:], replacement))


def _rename(term, prefix):
    if term[0] == "v":
        return ("v", (prefix, term[1]))
    return ("o", _rename(term[1], prefix), _rename(term[2], prefix))


def _canonical_pair(left, right):
    """Alpha-normalize, then make equality symmetry part of the key."""
    def one(a, b):
        names = {}

        def visit(term):
            if term[0] == "v":
                if term[1] not in names:
                    names[term[1]] = len(names)
                return ("v", names[term[1]])
            return ("o", visit(term[1]), visit(term[2]))

        return visit(a), visit(b), names

    a1, b1, m1 = one(left, right)
    b2, a2, m2 = one(right, left)
    if (b2, a2) < (a1, b1):
        return b2, a2, m2, True
    return a1, b1, m1, False


def _lean(term):
    if term[0] == "v":
        return ("X" + str(term[1])
                if isinstance(term[1], int) else str(term[1]))
    return "(" + _lean(term[1]) + " ◇ " + _lean(term[2]) + ")"


def _context_lean(term, path):
    if not path:
        return "q"
    if path[0] == 1:
        return "(" + _context_lean(term[1], path[1:]) + " ◇ " + _lean(term[2]) + ")"
    return "(" + _lean(term[1]) + " ◇ " + _context_lean(term[2], path[1:]) + ")"


class Equation:
    __slots__ = ("left", "right", "parents", "serial")

    def __init__(self, left, right, parents, serial):
        self.left = left
        self.right = right
        self.parents = parents
        self.serial = serial


def _collapse(equation):
    """Return the fresh variable index and which side it occupies."""
    if equation.left[0] == "v" and equation.left[1] not in _vars(equation.right):
        return equation.left[1], True
    if equation.right[0] == "v" and equation.right[1] not in _vars(equation.left):
        return equation.right[1], False
    return None


def _application(name, args, reverse=False):
    body = name
    if args:
        body += " " + " ".join(_lean(arg) for arg in args)
    if reverse:
        return "(" + body + ").symm"
    return body


def _superpose(source, target, source_reverse, target_reverse, path, serial):
    """Rewrite the selected side of target with the selected source direction."""
    sl = source.right if source_reverse else source.left
    sr = source.left if source_reverse else source.right
    tl = target.right if target_reverse else target.left
    tr = target.left if target_reverse else target.right
    sl, sr = _rename(sl, (serial, "s")), _rename(sr, (serial, "s"))
    tl, tr = _rename(tl, (serial, "t")), _rename(tr, (serial, "t"))
    subterm = tl
    for step in path:
        subterm = subterm[step]
    unifier = _unify(sl, subterm)
    if unifier is None:
        return None
    before = _subst(tl, unifier)
    replacement = _subst(sr, unifier)
    after = _replace(before, path, replacement)
    other = _subst(tr, unifier)
    if after == other:
        return None

    left, right, renaming, swapped = _canonical_pair(after, other)
    inverse = {old: new for old, new in renaming.items()}

    def canon(term):
        term = _subst(term, unifier)

        def visit(t):
            if t[0] == "v":
                # A parent variable can disappear with the rewritten subterm.
                # Its instance is then arbitrary; reuse the first result binder.
                return ("v", inverse.get(t[1], 0))
            return ("o", visit(t[1]), visit(t[2]))

        return visit(term)

    source_prefix = (serial, "s")
    target_prefix = (serial, "t")
    source_args = [canon(("v", (source_prefix, i)))
                   for i in range(1 + max(_vars(source.left) | _vars(source.right),
                                          default=-1))]
    target_args = [canon(("v", (target_prefix, i)))
                   for i in range(1 + max(_vars(target.left) | _vars(target.right),
                                          default=-1))]
    before_canon = canon(before)
    parents = (source, target, source_args, target_args, source_reverse,
               target_reverse, path, before_canon, swapped)
    return Equation(left, right, parents, serial)


def _search(initial_left, initial_right, deadline):
    left, right, renaming, swapped = _canonical_pair(initial_left, initial_right)
    original_vars = []

    def collect(term):
        if term[0] == "v" and term[1] not in original_vars:
            original_vars.append(term[1])
        elif term[0] == "o":
            collect(term[1])
            collect(term[2])

    collect(initial_left)
    collect(initial_right)
    h_args = [renaming[name] for name in original_vars]
    initial = Equation(left, right, ("h", swapped, h_args), 0)
    equations = []
    known = set()
    queue = []
    counter = 0

    def add(equation):
        nonlocal counter
        key = (equation.left, equation.right)
        if key in known:
            return None
        known.add(key)
        weight = _size(equation.left) + _size(equation.right)
        variable_count = len(_vars(equation.left) | _vars(equation.right))
        heapq.heappush(queue, (weight + 2 * variable_count, weight,
                               variable_count, counter, equation))
        counter += 1
        return _collapse(equation)

    collapse = add(initial)
    if collapse:
        return initial, collapse

    selected = 0
    while queue and len(known) < 18000 and time.monotonic() < deadline:
        _, _, _, _, given = heapq.heappop(queue)
        partners = equations + [given]
        equations.append(given)
        selected += 1
        for other in partners:
            for source, target in ((given, other), (other, given)):
                for sr in (False, True):
                    source_lhs = source.right if sr else source.left
                    if source_lhs[0] == "v":
                        continue
                    for tr in (False, True):
                        target_lhs = target.right if tr else target.left
                        for path, _ in _positions(target_lhs):
                            serial = selected * 100000 + counter
                            result = _superpose(source, target, sr, tr, path, serial)
                            if result is None:
                                continue
                            size = _size(result.left) + _size(result.right)
                            if size > 42 or len(_vars(result.left) | _vars(result.right)) > 8:
                                continue
                            collapse = add(result)
                            if collapse:
                                return result, collapse
                            if len(known) >= 18000 or time.monotonic() >= deadline:
                                break
                        if len(known) >= 18000 or time.monotonic() >= deadline:
                            break
                    if len(known) >= 18000 or time.monotonic() >= deadline:
                        break
                if len(known) >= 18000 or time.monotonic() >= deadline:
                    break
            if len(known) >= 18000 or time.monotonic() >= deadline:
                break
    return None, None


def _dependencies(root):
    result = []
    seen = set()

    def visit(equation):
        if equation.serial in seen:
            return
        seen.add(equation.serial)
        if equation.parents[0] != "h":
            visit(equation.parents[0])
            visit(equation.parents[1])
        result.append(equation)

    visit(root)
    return result


def _emit(eq2_text, root, collapse):
    dependencies = _dependencies(root)
    names = {equation.serial: "e" + str(i)
             for i, equation in enumerate(dependencies)}
    lines = ["import JudgeProblem", "", "def submission : Goal := by",
             "  intro G _ h"]
    for equation in dependencies:
        name = names[equation.serial]
        variables = sorted(_vars(equation.left) | _vars(equation.right))
        binders = " ".join("X" + str(v) for v in variables)
        lines.append("  have " + name + " (" + binders + " : G) : "
                     + _lean(equation.left) + " = " + _lean(equation.right) + " := by")
        if equation.parents[0] == "h":
            reverse = equation.parents[1]
            h_args = equation.parents[2]
            app = "h" + (" " + " ".join("X" + str(v) for v in h_args)
                         if h_args else "")
            lines.append("    exact " + ("(" + app + ").symm" if reverse else app))
            continue
        (source, target, source_args, target_args, source_reverse,
         target_reverse, path, before, swapped) = equation.parents
        source_app = _application(names[source.serial], source_args, source_reverse)
        target_app = _application(names[target.serial], target_args, target_reverse)
        context = _context_lean(before, path)
        congr = "congrArg (fun q => " + context + ") (" + source_app + ")"
        proof = "(" + congr + ").symm.trans (" + target_app + ")"
        if swapped:
            proof = "(" + proof + ").symm"
        lines.append("    exact " + proof)

    root_name = names[root.serial]
    index, variable_is_left = collapse
    all_vars = sorted(_vars(root.left) | _vars(root.right))
    args_a = [("v", "a") for _ in all_vars]
    args_b = [("v", "a") for _ in all_vars]
    args_b[index] = ("v", "b")
    app_a = _application(root_name, args_a)
    app_b = _application(root_name, args_b)
    if variable_is_left:
        singleton_proof = "(" + app_a + ").trans (" + app_b + ").symm"
    else:
        singleton_proof = "(" + app_a + ").symm.trans (" + app_b + ")"
    lines.append("  have singleton : ∀ a b : G, a = b := by")
    lines.append("    intro a b")
    lines.append("    exact " + singleton_proof)

    goal = _SPParser(eq2_text).equation()
    goal_vars = []
    seen = set()

    def collect_goal(term):
        if term[0] == "v" and term[1] not in seen:
            seen.add(term[1])
            goal_vars.append(term[1])
        elif term[0] == "o":
            collect_goal(term[1])
            collect_goal(term[2])

    collect_goal(goal[0])
    collect_goal(goal[1])
    if goal_vars:
        lines.append("  intro " + " ".join(goal_vars))
    lines.append("  exact singleton _ _")
    return "\n".join(lines) + "\n"


def singleton_forced_cert(eq1_text, eq2_text, time_budget_s=20.0):
    """Return a complete Lean certificate, or None if search fails."""
    try:
        initial = _SPParser(eq1_text).equation()
        _SPParser(eq2_text).equation()
        budget = max(0.01, float(time_budget_s))
    except (_SPParseError, TypeError, ValueError):
        return None
    root, collapse = _search(initial[0], initial[1], time.monotonic() + budget)
    if root is None:
        return None
    return _emit(eq2_text, root, collapse)



# ---------------------------------------------------------------------------
# General (non-singleton) TRUE prover: goal-directed bounded superposition.
# Runs completion on the hypothesis until the goal equation is joinable
# (both sides rewrite to a common term, meet-in-the-middle with bounded
# expansions), then replays the derivation + the goal rewrite chain as a
# self-contained Lean certificate (have-lemmas + congrArg/.symm/.trans).
# Namespaced (_g2*/_G2*) so it does not clobber the singleton prover above.
# Pure stdlib, deterministic, judge-verified.
# ---------------------------------------------------------------------------
class _G2ParseError(ValueError):
    pass


class _G2Parser:
    def __init__(self, source):
        self.tokens = re.findall(r"[a-z]|[()=]|◇", source)
        compact = re.sub(r"\s+", "", source)
        if "".join(self.tokens) != compact:
            raise _G2ParseError("invalid equation")
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def take(self, expected=None):
        token = self.peek()
        if token is None or (expected is not None and token != expected):
            raise _G2ParseError("unexpected token")
        self.pos += 1
        return token

    def atom(self):
        if self.peek() == "(":
            self.take("(")
            result = self.expr()
            self.take(")")
            return result
        token = self.take()
        if not (len(token) == 1 and token.islower()):
            raise _G2ParseError("expected variable")
        return ("v", token)

    def expr(self):
        result = self.atom()
        while self.peek() == "◇":
            self.take()
            result = ("o", result, self.atom())
        return result

    def equation(self):
        left = self.expr()
        self.take("=")
        right = self.expr()
        if self.peek() is not None:
            raise _G2ParseError("trailing input")
        return left, right


def _g2_size(term):
    return 1 if term[0] == "v" else 1 + _g2_size(term[1]) + _g2_size(term[2])


def _g2_vars(term, out=None):
    if out is None:
        out = set()
    if term[0] == "v":
        out.add(term[1])
    else:
        _g2_vars(term[1], out)
        _g2_vars(term[2], out)
    return out


def _g2_subst(term, substitution):
    while term[0] == "v" and term[1] in substitution:
        replacement = substitution[term[1]]
        if replacement == term:
            break
        term = replacement
    if term[0] == "v":
        return term
    return ("o", _g2_subst(term[1], substitution), _g2_subst(term[2], substitution))


def _g2_occurs(variable, term, substitution):
    term = _g2_subst(term, substitution)
    if term[0] == "v":
        return term[1] == variable
    return (_g2_occurs(variable, term[1], substitution)
            or _g2_occurs(variable, term[2], substitution))


def _g2_unify(left, right):
    substitution = {}
    pending = [(left, right)]
    while pending:
        a, b = pending.pop()
        a, b = _g2_subst(a, substitution), _g2_subst(b, substitution)
        if a == b:
            continue
        if a[0] == "v":
            if _g2_occurs(a[1], b, substitution):
                return None
            substitution[a[1]] = b
        elif b[0] == "v":
            if _g2_occurs(b[1], a, substitution):
                return None
            substitution[b[1]] = a
        elif a[0] == "o" and b[0] == "o":
            pending.append((a[1], b[1]))
            pending.append((a[2], b[2]))
        else:
            return None
    return {name: _g2_subst(value, substitution)
            for name, value in substitution.items()}


def _g2_match(pattern, target, substitution):
    """One-way first-order matching (variables occur only in pattern)."""
    if pattern[0] == "v":
        old = substitution.get(pattern[1])
        if old is None:
            substitution[pattern[1]] = target
            return True
        return old == target
    return (target[0] == "o"
            and _g2_match(pattern[1], target[1], substitution)
            and _g2_match(pattern[2], target[2], substitution))


def _g2_positions(term, path=()):
    yield path, term
    if term[0] == "o":
        yield from _g2_positions(term[1], path + (1,))
        yield from _g2_positions(term[2], path + (2,))


def _g2_nonvar_positions(term, path=()):
    if term[0] != "o":
        return
    yield path, term
    yield from _g2_nonvar_positions(term[1], path + (1,))
    yield from _g2_nonvar_positions(term[2], path + (2,))


def _g2_replace(term, path, replacement):
    if not path:
        return replacement
    if path[0] == 1:
        return ("o", _g2_replace(term[1], path[1:], replacement), term[2])
    return ("o", term[1], _g2_replace(term[2], path[1:], replacement))


def _g2_rename(term, prefix):
    if term[0] == "v":
        return ("v", (prefix, term[1]))
    return ("o", _g2_rename(term[1], prefix), _g2_rename(term[2], prefix))


def _g2_canonical_pair(left, right):
    """Alpha-normalize, with equality symmetry included in the key."""
    def one(a, b):
        names = {}

        def visit(term):
            if term[0] == "v":
                if term[1] not in names:
                    names[term[1]] = len(names)
                return ("v", names[term[1]])
            return ("o", visit(term[1]), visit(term[2]))

        return visit(a), visit(b), names

    a1, b1, m1 = one(left, right)
    b2, a2, m2 = one(right, left)
    if (b2, a2) < (a1, b1):
        return b2, a2, m2, True
    return a1, b1, m1, False


def _g2_lean(term):
    if term[0] == "v":
        return "X" + str(term[1]) if isinstance(term[1], int) else str(term[1])
    return "(" + _g2_lean(term[1]) + " ◇ " + _g2_lean(term[2]) + ")"


def _g2_context_lean(term, path):
    if not path:
        return "q"
    if path[0] == 1:
        return "(" + _g2_context_lean(term[1], path[1:]) + " ◇ " + _g2_lean(term[2]) + ")"
    return "(" + _g2_lean(term[1]) + " ◇ " + _g2_context_lean(term[2], path[1:]) + ")"


def _g2_term_code(term):
    if term[0] == "v":
        return "v" + str(term[1])
    return "o(" + _g2_term_code(term[1]) + "," + _g2_term_code(term[2]) + ")"


def _g2_reduction_key(term):
    return _g2_size(term), _g2_term_code(term)


class _G2Equation:
    __slots__ = ("left", "right", "parents", "serial")

    def __init__(self, left, right, parents, serial):
        self.left = left
        self.right = right
        self.parents = parents
        self.serial = serial


class _G2RewriteStep:
    __slots__ = ("before", "after", "equation", "args", "reverse", "path")

    def __init__(self, before, after, equation, args, reverse, path):
        self.before = before
        self.after = after
        self.equation = equation
        self.args = args
        self.reverse = reverse
        self.path = path


def _g2_application(name, args, reverse=False):
    body = name
    if args:
        body += " " + " ".join(_g2_lean(arg) for arg in args)
    if reverse:
        return "(" + body + ").symm"
    return body


def _g2_superpose(source, target, source_reverse, target_reverse, path, serial):
    sl = source.right if source_reverse else source.left
    sr = source.left if source_reverse else source.right
    tl = target.right if target_reverse else target.left
    tr = target.left if target_reverse else target.right
    sl, sr = _g2_rename(sl, (serial, "s")), _g2_rename(sr, (serial, "s"))
    tl, tr = _g2_rename(tl, (serial, "t")), _g2_rename(tr, (serial, "t"))
    subterm = tl
    for step in path:
        subterm = subterm[step]
    unifier = _g2_unify(sl, subterm)
    if unifier is None:
        return None
    before = _g2_subst(tl, unifier)
    after = _g2_replace(before, path, _g2_subst(sr, unifier))
    other = _g2_subst(tr, unifier)
    if after == other:
        return None

    left, right, renaming, swapped = _g2_canonical_pair(after, other)
    inverse = {old: new for old, new in renaming.items()}

    def canon(term):
        term = _g2_subst(term, unifier)

        def visit(t):
            if t[0] == "v":
                return ("v", inverse.get(t[1], 0))
            return ("o", visit(t[1]), visit(t[2]))

        return visit(term)

    sp = (serial, "s")
    tp = (serial, "t")
    source_args = [canon(("v", (sp, i)))
                   for i in range(1 + max(_g2_vars(source.left) | _g2_vars(source.right),
                                          default=-1))]
    target_args = [canon(("v", (tp, i)))
                   for i in range(1 + max(_g2_vars(target.left) | _g2_vars(target.right),
                                          default=-1))]
    parents = (source, target, source_args, target_args, source_reverse,
               target_reverse, path, canon(before), swapped)
    return _G2Equation(left, right, parents, serial)


def _g2_goal_variables(goal):
    result = []
    seen = set()

    def visit(term):
        if term[0] == "v":
            if term[1] not in seen:
                seen.add(term[1])
                result.append(term[1])
        else:
            visit(term[1])
            visit(term[2])

    visit(goal[0])
    visit(goal[1])
    return result


def _g2_equation_args(equation, substitution, default):
    count = 1 + max(_g2_vars(equation.left) | _g2_vars(equation.right), default=-1)
    return [substitution.get(i, default) for i in range(count)]


def _g2_direct_step(equation, left, right, default):
    for reverse in (False, True):
        lhs = equation.right if reverse else equation.left
        rhs = equation.left if reverse else equation.right
        substitution = {}
        if (_g2_match(lhs, left, substitution)
                and _g2_match(rhs, right, substitution)):
            return _G2RewriteStep(left, right, equation,
                               _g2_equation_args(equation, substitution, default),
                               reverse, ())
    return None


def _g2_normal_form(start, equations, default, max_steps=80):
    """Greedily take the least strictly decreasing one-step reduct."""
    current = start
    steps = []
    for _ in range(max_steps):
        current_key = _g2_reduction_key(current)
        best = None
        best_key = None
        for path, subterm in _g2_positions(current):
            for equation in equations:
                for reverse in (False, True):
                    lhs = equation.right if reverse else equation.left
                    rhs = equation.left if reverse else equation.right
                    substitution = {}
                    if not _g2_match(lhs, subterm, substitution):
                        continue
                    # Variables present only on the replacement side are legal
                    # universally quantified parameters.  Pick a fixed in-scope
                    # goal term for a deterministic instance.
                    instance = dict(substitution)
                    for variable in _g2_vars(rhs):
                        if variable not in instance:
                            instance[variable] = default
                    replacement = _g2_subst(rhs, instance)
                    after = _g2_replace(current, path, replacement)
                    key = _g2_reduction_key(after)
                    if key >= current_key:
                        continue
                    choice_key = (key, len(path), equation.serial, reverse)
                    if best_key is None or choice_key < best_key:
                        args = _g2_equation_args(equation, substitution, default)
                        best = _G2RewriteStep(current, after, equation, args,
                                           reverse, path)
                        best_key = choice_key
        if best is None:
            break
        steps.append(best)
        current = best.after
    return current, steps


def _g2_join_goal(goal, equations):
    goal_vars = _g2_goal_variables(goal)
    default = ("v", goal_vars[0]) if goal_vars else goal[0]

    # Subsumption catches a generated generalization of the goal without
    # depending on the chosen reduction ordering.
    for equation in equations:
        direct = _g2_direct_step(equation, goal[0], goal[1], default)
        if direct is not None:
            return [direct], []

    left_nf, left_steps = _g2_normal_form(goal[0], equations, default)
    right_nf, right_steps = _g2_normal_form(goal[1], equations, default)
    if left_nf == right_nf:
        return left_steps, right_steps
    return None


def _g2_subterms(terms):
    result = []
    seen = set()
    for root in terms:
        for _, term in _g2_positions(root):
            if term not in seen:
                seen.add(term)
                result.append(term)
    result.sort(key=_g2_reduction_key)
    return result


def _g2_rewrite_neighbors(term, equations, pool, size_limit, deadline):
    """Yield a bounded, deterministic set of witnessed rewrites in both directions."""
    yielded = 0
    for path, subterm in _g2_positions(term):
        for equation in equations:
            equation_vars = sorted(_g2_vars(equation.left) | _g2_vars(equation.right))
            for reverse in (False, True):
                lhs = equation.right if reverse else equation.left
                rhs = equation.left if reverse else equation.right
                substitution = {}
                if not _g2_match(lhs, subterm, substitution):
                    continue
                missing = [v for v in equation_vars if v not in substitution]
                if not missing:
                    assignments = [()]
                elif len(missing) <= 3:
                    assignments = itertools.islice(
                        itertools.product(pool, repeat=len(missing)), 160)
                else:
                    # Wide unconstrained rules otherwise create an unhelpful
                    # Cartesian explosion.  Diagonal instances still include
                    # every natural goal subterm choice.
                    assignments = ((value,) * len(missing) for value in pool)
                for values in assignments:
                    instance = dict(substitution)
                    instance.update(zip(missing, values))
                    replacement = _g2_subst(rhs, instance)
                    after = _g2_replace(term, path, replacement)
                    if after == term or _g2_size(after) > size_limit:
                        continue
                    args = [instance[v] for v in equation_vars]
                    yield after, _G2RewriteStep(term, after, equation, args,
                                             reverse, path)
                    yielded += 1
                    if yielded >= 5000 or time.monotonic() >= deadline:
                        return


def _g2_bounded_join(goal, equations, deadline, max_depth=3):
    """Meet-in-the-middle goal rewriting, allowing temporary expansions."""
    if time.monotonic() >= deadline:
        return None
    ranked = sorted(
        equations,
        key=lambda e: (_g2_size(e.left) + _g2_size(e.right),
                       len(_g2_vars(e.left) | _g2_vars(e.right)), e.serial),
    )[:96]
    pool = _g2_subterms(goal)
    size_limit = max(_g2_size(goal[0]), _g2_size(goal[1])) + 24
    left_seen = {goal[0]: []}
    right_seen = {goal[1]: []}
    left_front = [goal[0]]
    right_front = [goal[1]]

    for _ in range(max_depth):
        for from_left in (True, False):
            own = left_seen if from_left else right_seen
            other = right_seen if from_left else left_seen
            front = left_front if from_left else right_front
            new_front = []
            for term in front:
                prefix = own[term]
                for after, step in _g2_rewrite_neighbors(
                        term, ranked, pool, size_limit, deadline):
                    if after in own:
                        continue
                    path = prefix + [step]
                    own[after] = path
                    if after in other:
                        if from_left:
                            return path, other[after]
                        return other[after], path
                    if len(own) < 3500:
                        new_front.append(after)
                    if len(own) >= 3500 or time.monotonic() >= deadline:
                        break
                if len(own) >= 3500 or time.monotonic() >= deadline:
                    break
            if from_left:
                left_front = new_front
            else:
                right_front = new_front
            if time.monotonic() >= deadline:
                return None
        if not left_front and not right_front:
            break
    return None


def _g2_search(initial_pair, goal, deadline):
    started = time.monotonic()
    remaining = max(0.0, deadline - started)
    saturation_deadline = deadline - min(1.5, remaining * 0.12)
    initial_left, initial_right = initial_pair
    left, right, renaming, swapped = _g2_canonical_pair(initial_left, initial_right)
    original_vars = []

    def collect(term):
        if term[0] == "v" and term[1] not in original_vars:
            original_vars.append(term[1])
        elif term[0] == "o":
            collect(term[1])
            collect(term[2])

    collect(initial_left)
    collect(initial_right)
    initial = _G2Equation(left, right,
                       ("h", swapped, [renaming[v] for v in original_vars]), 0)
    selected_equations = []
    all_equations = []
    known = set()
    queue = []
    counter = 0

    def add(equation):
        nonlocal counter
        key = (equation.left, equation.right)
        if key in known:
            return False
        known.add(key)
        all_equations.append(equation)
        weight = _g2_size(equation.left) + _g2_size(equation.right)
        variable_count = len(_g2_vars(equation.left) | _g2_vars(equation.right))
        heapq.heappush(queue, (weight + 2 * variable_count, weight,
                               variable_count, counter, equation))
        counter += 1
        return True

    add(initial)
    joined = _g2_join_goal(goal, all_equations)
    if joined is not None:
        return joined
    joined = _g2_bounded_join(goal, all_equations, min(deadline, time.monotonic() + 0.35))
    if joined is not None:
        return joined

    selected = 0
    last_join_count = 0
    max_known = 40000
    while (queue and len(known) < max_known
           and time.monotonic() < saturation_deadline):
        _, _, _, _, given = heapq.heappop(queue)
        partners = selected_equations + [given]
        selected_equations.append(given)
        selected += 1
        added_this_round = 0
        for other in partners:
            for source, target in ((given, other), (other, given)):
                for source_reverse in (False, True):
                    source_lhs = source.right if source_reverse else source.left
                    if source_lhs[0] == "v":
                        continue
                    for target_reverse in (False, True):
                        target_lhs = target.right if target_reverse else target.left
                        for path, _ in _g2_nonvar_positions(target_lhs):
                            serial = selected * 100000 + counter
                            result = _g2_superpose(source, target, source_reverse,
                                               target_reverse, path, serial)
                            if result is None:
                                continue
                            size = _g2_size(result.left) + _g2_size(result.right)
                            if (size > 46
                                    or len(_g2_vars(result.left) | _g2_vars(result.right)) > 9):
                                continue
                            if add(result):
                                added_this_round += 1
                                direct = _g2_direct_step(
                                    result, goal[0], goal[1],
                                    ("v", _g2_goal_variables(goal)[0]),
                                )
                                if direct is not None:
                                    return [direct], []
                            if (len(known) >= max_known
                                    or time.monotonic() >= saturation_deadline):
                                break
                        if (len(known) >= max_known
                                or time.monotonic() >= saturation_deadline):
                            break
                    if (len(known) >= max_known
                            or time.monotonic() >= saturation_deadline):
                        break
                if (len(known) >= max_known
                        or time.monotonic() >= saturation_deadline):
                    break
            if (len(known) >= max_known
                    or time.monotonic() >= saturation_deadline):
                break

        # Normalisation is more expensive than direct subsumption.  Run it
        # after productive given-clause rounds, with a modest batching floor.
        if (added_this_round and
                (len(all_equations) - last_join_count >= 12 or selected < 8)):
            joined = _g2_join_goal(goal, all_equations)
            last_join_count = len(all_equations)
            if joined is not None:
                return joined
    # Use any completion consequences found before the deadline in a final
    # expansion-capable join attempt.  It returns promptly when no time remains.
    joined = _g2_bounded_join(goal, all_equations, deadline)
    if joined is not None:
        return joined
    return None


def _g2_dependencies(roots):
    result = []
    seen = set()

    def visit(equation):
        if equation.serial in seen:
            return
        seen.add(equation.serial)
        if equation.parents[0] != "h":
            visit(equation.parents[0])
            visit(equation.parents[1])
        result.append(equation)

    for equation in roots:
        visit(equation)
    return result


def _g2_step_proof(step, names):
    app = _g2_application(names[step.equation.serial], step.args, step.reverse)
    if not step.path:
        return app
    context = _g2_context_lean(step.before, step.path)
    return "congrArg (fun q => " + context + ") (" + app + ")"


def _g2_emit(goal, joined):
    left_steps, right_steps = joined
    roots = [step.equation for step in left_steps + right_steps]
    dependencies = _g2_dependencies(roots)
    names = {equation.serial: "e" + str(i)
             for i, equation in enumerate(dependencies)}
    lines = ["import JudgeProblem", "", "def submission : Goal := by",
             "  intro G _ h"]

    for equation in dependencies:
        name = names[equation.serial]
        variables = sorted(_g2_vars(equation.left) | _g2_vars(equation.right))
        binders = " ".join("X" + str(v) for v in variables)
        lines.append("  have " + name + " (" + binders + " : G) : "
                     + _g2_lean(equation.left) + " = " + _g2_lean(equation.right)
                     + " := by")
        if equation.parents[0] == "h":
            reverse = equation.parents[1]
            h_args = equation.parents[2]
            app = "h" + (" " + " ".join("X" + str(v) for v in h_args)
                         if h_args else "")
            lines.append("    exact " + ("(" + app + ").symm" if reverse else app))
            continue
        (source, target, source_args, target_args, source_reverse,
         target_reverse, path, before, swapped) = equation.parents
        source_app = _g2_application(names[source.serial], source_args, source_reverse)
        target_app = _g2_application(names[target.serial], target_args, target_reverse)
        context = _g2_context_lean(before, path)
        congr = "congrArg (fun q => " + context + ") (" + source_app + ")"
        proof = "(" + congr + ").symm.trans (" + target_app + ")"
        if swapped:
            proof = "(" + proof + ").symm"
        lines.append("    exact " + proof)

    goal_vars = _g2_goal_variables(goal)
    if goal_vars:
        lines.append("  intro " + " ".join(goal_vars))

    goal_step_names = []
    for index, step in enumerate(left_steps + right_steps):
        name = "g" + str(index)
        goal_step_names.append(name)
        lines.append("  have " + name + " : " + _g2_lean(step.before) + " = "
                     + _g2_lean(step.after) + " := by")
        lines.append("    exact " + _g2_step_proof(step, names))

    left_names = goal_step_names[:len(left_steps)]
    right_names = goal_step_names[len(left_steps):]

    def chain(names_):
        if not names_:
            return "rfl"
        result = names_[0]
        for name in names_[1:]:
            result = "(" + result + ").trans " + name
        return result

    if not left_steps and not right_steps:
        lines.append("  exact rfl")
    elif not right_steps:
        lines.append("  exact " + chain(left_names))
    elif not left_steps:
        lines.append("  exact (" + chain(right_names) + ").symm")
    else:
        lines.append("  exact (" + chain(left_names) + ").trans ("
                     + chain(right_names) + ").symm")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# G3: ordered unit-equational superposition prover (unfailing completion with
# a negated-goal clause), proof-producing.  Terms: ("v", name) variables,
# ("k", name) goal constants (Skolemised goal variables), ("o", a, b) the
# magma operation.  Equations are stored with the KBO-larger side on the left
# when orientable; inferences are restricted by the ordering; new equations
# and goal clauses are demodulated by the oriented active rules.  Every
# derived equation keeps its derivation so the search result is replayed as a
# self-contained Lean certificate (have-lemmas, congrArg/.symm/.trans).
# ---------------------------------------------------------------------------


class _G3ParseError(ValueError):
    pass


class _G3Parser:
    def __init__(self, source):
        self.tokens = re.findall(r"[a-z]|[()=]|◇", source)
        compact = re.sub(r"\s+", "", source)
        if "".join(self.tokens) != compact:
            raise _G3ParseError("invalid equation")
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def take(self, expected=None):
        token = self.peek()
        if token is None or (expected is not None and token != expected):
            raise _G3ParseError("unexpected token")
        self.pos += 1
        return token

    def atom(self):
        if self.peek() == "(":
            self.take("(")
            result = self.expr()
            self.take(")")
            return result
        token = self.take()
        if not (len(token) == 1 and token.islower()):
            raise _G3ParseError("expected variable")
        return ("v", token)

    def expr(self):
        result = self.atom()
        while self.peek() == "◇":
            self.take()
            result = ("o", result, self.atom())
        return result

    def equation(self):
        left = self.expr()
        self.take("=")
        right = self.expr()
        if self.peek() is not None:
            raise _G3ParseError("trailing input")
        return left, right


def _g3_size(term):
    if term[0] != "o":
        return 1
    return 1 + _g3_size(term[1]) + _g3_size(term[2])


def _g3_vars(term, out=None):
    if out is None:
        out = set()
    if term[0] == "v":
        out.add(term[1])
    elif term[0] == "o":
        _g3_vars(term[1], out)
        _g3_vars(term[2], out)
    return out


def _g3_varcount(term, out):
    if term[0] == "v":
        out[term[1]] = out.get(term[1], 0) + 1
    elif term[0] == "o":
        _g3_varcount(term[1], out)
        _g3_varcount(term[2], out)


def _g3_subst(term, substitution):
    while term[0] == "v" and term[1] in substitution:
        replacement = substitution[term[1]]
        if replacement == term:
            break
        term = replacement
    if term[0] != "o":
        return term
    return ("o", _g3_subst(term[1], substitution), _g3_subst(term[2], substitution))


def _g3_occurs(variable, term, substitution):
    stack = [term]
    while stack:
        t = stack.pop()
        while t[0] == "v" and t[1] in substitution:
            t = substitution[t[1]]
        if t[0] == "v":
            if t[1] == variable:
                return True
        elif t[0] == "o":
            stack.append(t[1])
            stack.append(t[2])
    return False


def _g3_unify(left, right):
    substitution = {}
    pending = [(left, right)]
    while pending:
        a, b = pending.pop()
        while a[0] == "v" and a[1] in substitution:
            a = substitution[a[1]]
        while b[0] == "v" and b[1] in substitution:
            b = substitution[b[1]]
        if a == b:
            continue
        if a[0] == "v":
            if _g3_occurs(a[1], b, substitution):
                return None
            substitution[a[1]] = b
        elif b[0] == "v":
            if _g3_occurs(b[1], a, substitution):
                return None
            substitution[b[1]] = a
        elif a[0] == "o" and b[0] == "o":
            pending.append((a[1], b[1]))
            pending.append((a[2], b[2]))
        else:
            return None
    return substitution


def _g3_inst_size(term, substitution, memo):
    """Size of term under a (triangular) substitution without building it."""
    total = 0
    stack = [term]
    while stack:
        t = stack.pop()
        tag = t[0]
        if tag == "o":
            total += 1
            stack.append(t[1])
            stack.append(t[2])
        elif tag == "v":
            bound = substitution.get(t[1])
            if bound is None:
                total += 1
            else:
                size = memo.get(t[1])
                if size is None:
                    size = _g3_inst_size(bound, substitution, memo)
                    memo[t[1]] = size
                total += size
        else:
            total += 1
    return total


def _g3_counted_size(static_size, counts, prefix, substitution, memo):
    """Instantiated size of a term from its static size and variable counts."""
    total = static_size
    for variable, n in counts.items():
        name = (prefix, variable)
        bound = substitution.get(name)
        if bound is not None:
            size = memo.get(name)
            if size is None:
                size = _g3_inst_size(bound, substitution, memo)
                memo[name] = size
            total += n * (size - 1)
    return total


def _g3_subst_m(term, substitution, memo):
    """Apply a (triangular) substitution; instantiated bindings are memoised
    and shared, unchanged subterms are returned as the same object."""
    tag = term[0]
    if tag == "v":
        name = term[1]
        bound = substitution.get(name)
        if bound is None:
            return term
        result = memo.get(name)
        if result is None:
            result = _g3_subst_m(bound, substitution, memo)
            memo[name] = result
        return result
    if tag != "o":
        return term
    a = _g3_subst_m(term[1], substitution, memo)
    b = _g3_subst_m(term[2], substitution, memo)
    if a is term[1] and b is term[2]:
        return term
    return ("o", a, b)


def _g3_match(pattern, target, substitution):
    """One-way matching (pattern variables bind to target subterms)."""
    stack = [(pattern, target)]
    pop = stack.pop
    push = stack.append
    get = substitution.get
    while stack:
        pattern, target = pop()
        tag = pattern[0]
        if tag == "v":
            old = get(pattern[1])
            if old is None:
                substitution[pattern[1]] = target
            elif old is not target and old != target:
                return False
        elif tag == "o":
            if target[0] != "o":
                return False
            push((pattern[2], target[2]))
            push((pattern[1], target[1]))
        elif pattern != target:
            return False
    return True


def _g3_positions(term, path=()):
    """Non-variable, non-constant positions (root first)."""
    if term[0] != "o":
        return
    yield path, term
    yield from _g3_positions(term[1], path + (1,))
    yield from _g3_positions(term[2], path + (2,))


def _g3_replace(term, path, replacement):
    if not path:
        return replacement
    if path[0] == 1:
        return ("o", _g3_replace(term[1], path[1:], replacement), term[2])
    return ("o", term[1], _g3_replace(term[2], path[1:], replacement))


def _g3_rename(term, prefix):
    if term[0] == "v":
        return ("v", (prefix, term[1]))
    if term[0] != "o":
        return term
    return ("o", _g3_rename(term[1], prefix), _g3_rename(term[2], prefix))


_G3_SIZE_CACHE = {}
_G3_VC_CACHE = {}


def _g3_sz(term):
    """Cached term size (keyed by the term value; tuples hash in C)."""
    size = _G3_SIZE_CACHE.get(term)
    if size is None:
        size = _g3_size(term)
        if len(_G3_SIZE_CACHE) > 150000:
            _G3_SIZE_CACHE.clear()
        _G3_SIZE_CACHE[term] = size
    return size


def _g3_vc(term):
    """Cached variable-count dict of a term (read-only)."""
    counts = _G3_VC_CACHE.get(term)
    if counts is None:
        counts = {}
        _g3_varcount(term, counts)
        if len(_G3_VC_CACHE) > 150000:
            _G3_VC_CACHE.clear()
        _G3_VC_CACHE[term] = counts
    return counts


def _g3_gt(s, t, ws=None, wt=None):
    """Knuth-Bendix ordering, unit weights, single binary symbol."""
    if s == t:
        return False
    if ws is None:
        ws = _g3_sz(s)
    if wt is None:
        wt = _g3_sz(t)
    if ws < wt:
        return False
    if t[0] == "v":
        ct = {t[1]: 1}
    elif t[0] == "k":
        ct = None
    else:
        ct = _g3_vc(t)
    if ct:
        cs = _g3_vc(s) if s[0] == "o" else ({s[1]: 1} if s[0] == "v" else {})
        for v, n in ct.items():
            if cs.get(v, 0) < n:
                return False
    if ws > wt:
        return True
    return _g3_lex(s, t)


def _g3_lex(s, t):
    if s == t:
        return False
    if s[0] == "o" and t[0] == "o":
        if s[1] == t[1]:
            return _g3_lex(s[2], t[2])
        return _g3_gt(s[1], t[1])
    if s[0] == "k" and t[0] == "k":
        return s[1] > t[1]
    return False


def _g3_preorder(term):
    """Preorder symbol list plus subtree-end indices (for skeleton matching)."""
    syms = []
    ends = []
    # iterative preorder: stack of (term, index_to_close) where a closing
    # marker (None, i) records the end of subtree i
    stack = [(term, -1)]
    pop = stack.pop
    push = stack.append
    while stack:
        t, close = pop()
        if t is None:
            ends[close] = len(syms)
            continue
        i = len(syms)
        syms.append(t[0])
        ends.append(0)
        if t[0] == "o":
            push((None, i))
            push((t[2], -1))
            push((t[1], -1))
        else:
            ends[i] = i + 1
    return syms, ends


def _g3_positions_sized(term):
    """List of (path, subterm, size) for all non-leaf positions, root first."""
    out = []

    def visit(t, path):
        if t[0] != "o":
            return 1
        index = len(out)
        out.append(None)
        size = 1 + visit(t[1], path + (1,)) + visit(t[2], path + (2,))
        out[index] = (path, t, size)
        return size

    visit(term, ())
    return out


class _G3Index:
    """Discrimination tree over linear skeletons of rule sides."""

    def __init__(self):
        self.root = {}

    def add(self, term, entry):
        node = self.root
        syms, _ = _g3_preorder(term)
        for s in syms:
            node = node.setdefault("*" if s == "v" else "o", {})
        node.setdefault(None, []).append(entry)

    def lookup(self, term):
        syms, ends = _g3_preorder(term)
        n = len(syms)
        out = []
        stack = [(self.root, 0)]
        while stack:
            node, i = stack.pop()
            if i == n:
                entries = node.get(None)
                if entries:
                    out.extend(entries)
                continue
            child = node.get("*")
            if child is not None:
                stack.append((child, ends[i]))
            if syms[i] == "o":
                child = node.get("o")
                if child is not None:
                    stack.append((child, i + 1))
        return out


def _g3_lean(term):
    if term[0] == "v":
        return "X" + str(term[1]) if isinstance(term[1], int) else str(term[1])
    if term[0] == "k":
        return str(term[1])
    return "(" + _g3_lean(term[1]) + " ◇ " + _g3_lean(term[2]) + ")"


def _g3_context_lean(term, path):
    if not path:
        return "q"
    if path[0] == 1:
        return "(" + _g3_context_lean(term[1], path[1:]) + " ◇ " + _g3_lean(term[2]) + ")"
    return "(" + _g3_lean(term[1]) + " ◇ " + _g3_context_lean(term[2], path[1:]) + ")"


def _g3_application(name, args, reverse=False):
    body = name
    if args:
        body += " " + " ".join(_g3_lean(arg) for arg in args)
    if reverse:
        return "(" + body + ").symm"
    return body


class _G3Eq:
    __slots__ = ("left", "right", "parents", "serial", "weight", "nvars",
                 "lsize", "rsize", "depth", "_orient", "_sl", "_sr", "_tl",
                 "_tr", "_args", "recipe", "deleted", "_tpos", "_vc")

    def __init__(self, left, right, parents, serial, depth, nvars=None, recipe=None):
        self.left = left
        self.right = right
        self.parents = parents
        self.serial = serial
        self.depth = depth
        self.recipe = recipe
        self.deleted = False
        self.lsize = _g3_size(left)
        self.rsize = _g3_size(right)
        self.weight = self.lsize + self.rsize
        if nvars is None:
            nvars = len(_g3_vars(left) | _g3_vars(right))
        self.nvars = nvars
        self._orient = None
        self._sl = None
        self._sr = None
        self._tl = None
        self._tr = None
        self._args = None
        self._tpos = None
        self._vc = None

    def varcounts(self):
        """Cached (left counts, right counts) over the canonical variables."""
        if self._vc is None:
            lc, rc = {}, {}
            _g3_varcount(self.left, lc)
            _g3_varcount(self.right, rc)
            self._vc = (lc, rc)
        return self._vc

    def tpos(self, reverse):
        """Cached (path, subterm, size, varcounts) list of the t-renamed side."""
        if self._tpos is None:
            def build(side, raw):
                out = []
                for (path, subterm, size), (_, raw_sub, _) in zip(
                        _g3_positions_sized(side), _g3_positions_sized(raw)):
                    counts = {}
                    _g3_varcount(raw_sub, counts)
                    out.append((path, subterm, size, counts))
                return out
            self._tpos = (build(self.tl, self.left), build(self.tr, self.right))
        return self._tpos[1 if reverse else 0]

    @property
    def orient(self):
        if self._orient is None:
            self._orient = 1 if _g3_gt(self.left, self.right) else 0
        return self._orient

    @property
    def sl(self):
        if self._sl is None:
            self._sl = _g3_rename(self.left, "s")
        return self._sl

    @property
    def sr(self):
        if self._sr is None:
            self._sr = _g3_rename(self.right, "s")
        return self._sr

    @property
    def tl(self):
        if self._tl is None:
            self._tl = _g3_rename(self.left, "t")
        return self._tl

    @property
    def tr(self):
        if self._tr is None:
            self._tr = _g3_rename(self.right, "t")
        return self._tr

    def step_args(self):
        """(source_args, target_args, before) in this equation's binders."""
        if self._args is None:
            (source, target, unifier, names, before_raw, lazy_target,
             _, _, _, _) = self.parents

            def visit(t):
                if t[0] == "v":
                    return ("v", names.get(t[1], 0))
                if t[0] != "o":
                    return t
                return ("o", visit(t[1]), visit(t[2]))

            source_args = [visit(_g3_subst(("v", ("s", i)), unifier))
                           for i in range(source.nvars)]
            if lazy_target:
                target_args = [("v", names.get(i, 0)) for i in range(target.nvars)]
            else:
                target_args = [visit(_g3_subst(("v", ("t", i)), unifier))
                               for i in range(target.nvars)]
            self._args = (source_args, target_args, visit(before_raw))
        return self._args


class _G3Step:
    __slots__ = ("before", "after", "equation", "args", "reverse", "path")

    def __init__(self, before, after, equation, args, reverse, path):
        self.before = before
        self.after = after
        self.equation = equation
        self.args = args
        self.reverse = reverse
        self.path = path


class _G3Neg:
    __slots__ = ("left", "right", "parent", "sigma", "lsteps", "rsteps",
                 "serial", "weight", "depth")

    def __init__(self, left, right, parent, sigma, lsteps, rsteps, serial):
        self.left = left
        self.right = right
        self.parent = parent
        self.sigma = sigma
        self.lsteps = lsteps
        self.rsteps = rsteps
        self.serial = serial
        self.weight = _g3_size(left) + _g3_size(right)
        self.depth = 0 if parent is None else parent.depth + 1


def _g3_canonical(left, right):
    """Rename variables to 0..n-1 by first occurrence; return terms + map."""
    names = {}

    def visit(term):
        if term[0] == "v":
            if term[1] not in names:
                names[term[1]] = len(names)
            return ("v", names[term[1]])
        if term[0] != "o":
            return term
        return ("o", visit(term[1]), visit(term[2]))

    a = visit(left)
    b = visit(right)
    return a, b, names


def _g3_key(left, right):
    a1, b1, _ = _g3_canonical(left, right)
    b2, a2, _ = _g3_canonical(right, left)
    return min((a1, b1), (b2, a2))


def _g3_eq_key(eq):
    """Symmetric alpha-key of a stored (already canonical) equation."""
    if eq.lsize > eq.rsize:
        return (eq.left, eq.right)
    b2, a2, _ = _g3_canonical(eq.right, eq.left)
    if eq.lsize < eq.rsize:
        return (b2, a2)
    return min((eq.left, eq.right), (b2, a2))


class _G3Prover:
    def __init__(self, hypothesis, goal, deadline, size_cap=60, var_cap=10,
                 neg_size_cap=None, max_known=250000, age_ratio=6, var_penalty=2,
                 collapse_bonus=0, rhs_factor=1, max_neg=25000):
        _G3_SIZE_CACHE.clear()
        _G3_VC_CACHE.clear()
        self.deadline = deadline
        self.max_neg = max_neg
        self.nf_limit = 400000 if size_cap <= 60 else int(400000 * 60 / size_cap)
        self.var_penalty = var_penalty
        self.collapse_bonus = collapse_bonus
        self.rhs_factor = rhs_factor
        self.size_cap = size_cap
        self.var_cap = var_cap
        self.neg_size_cap = neg_size_cap or size_cap + 10
        self.max_known = max_known
        self.age_ratio = age_ratio
        self.known = set()          # hashes of symmetric alpha-keys
        self.neg_known = set()
        self.active = []
        self.active_neg = []
        self.index = _G3Index()     # demodulation candidates: (eq, reverse)
        self.queue = []             # weight-ordered passive (recipes)
        self.age_queue = []         # age-ordered passive (same recipes)
        self.age_pos = 0
        self.picked = set()         # counters already selected
        self.counter = 0
        self.serial = 0
        self.generated = 0
        self.selected = 0
        self.result = None
        self.clock = 0
        self.nf_set = {}
        self.ucache = {}            # (renamed lhs, renamed subterm) -> unifier
        self.rule_log = []
        self.version = 0
        hl, hr = hypothesis
        original = []

        def collect(term):
            if term[0] == "v":
                if term[1] not in original:
                    original.append(term[1])
            else:
                collect(term[1])
                collect(term[2])

        collect(hl)
        collect(hr)
        swapped = _g3_gt(hr, hl)
        if swapped:
            hl, hr = hr, hl
        a, b, names = _g3_canonical(hl, hr)
        h_args = [names[v] for v in original]
        self.h_eq = _G3Eq(a, b, ("h", swapped, h_args), self.next_serial(), 0,
                          recipe=("H",))
        self.known.add(hash(_g3_key(a, b)))
        self.push(self.h_eq)
        gl, gr = goal
        self.goal_vars = []

        def collect_goal(term):
            if term[0] == "v":
                if term[1] not in self.goal_vars:
                    self.goal_vars.append(term[1])
            else:
                collect_goal(term[1])
                collect_goal(term[2])

        collect_goal(gl)
        collect_goal(gr)

        def skolem(term):
            if term[0] == "v":
                return ("k", term[1])
            return ("o", skolem(term[1]), skolem(term[2]))

        self.goal = (skolem(gl), skolem(gr))
        neg = _G3Neg(self.goal[0], self.goal[1], None, {}, [], [], self.next_serial())
        self.neg_known.add(_g3_key(neg.left, neg.right))
        self.push_neg(neg)

    # -- bookkeeping ------------------------------------------------------
    def next_serial(self):
        self.serial += 1
        return self.serial

    def push(self, eq):
        priority = eq.lsize + self.rhs_factor * eq.rsize + self.var_penalty * eq.nvars
        if eq.right[0] == "v":
            priority -= self.collapse_bonus
        entry = (priority, 0, self.counter, eq.recipe)
        heapq.heappush(self.queue, entry)
        self.age_queue.append(entry)
        self.counter += 1

    def push_neg(self, neg):
        priority = neg.weight
        heapq.heappush(self.queue, (priority, 1, self.counter, neg))
        self.counter += 1

    def timed_out(self):
        self.clock += 1
        if self.clock & 63:
            return False
        return time.monotonic() >= self.deadline

    def pop(self):
        """Given-clause selection: weight-first with periodic oldest pick."""
        if self.age_ratio and self.selected % self.age_ratio == self.age_ratio - 1:
            while self.age_pos < len(self.age_queue):
                entry = self.age_queue[self.age_pos]
                self.age_pos += 1
                if entry[2] not in self.picked:
                    self.picked.add(entry[2])
                    return 0, entry[3]
            if self.age_pos > 0:
                del self.age_queue[:self.age_pos]
                self.age_pos = 0
        while self.queue:
            _, kind, counter, item = heapq.heappop(self.queue)
            if kind == 1:
                return 1, item
            if counter not in self.picked:
                self.picked.add(counter)
                return 0, item
        return None, None

    def replay(self, recipe):
        """Rebuild the full equation (with proof record) from its recipe."""
        if recipe[0] == "H":
            return self.h_eq
        if recipe[0] == "S":
            _, source, target, source_reverse, target_reverse, path = recipe
            return self.make_step(source, target, source_reverse, target_reverse,
                                  path, True)
        _, rule, sub, reverse, target_reverse, path = recipe
        eq = self.replay(sub)
        if eq is None:
            return None
        return self.make_step(rule, eq, reverse, target_reverse, path, False)

    def backward_simplify(self, rule):
        """Rewrite active equations reducible by the new rule; they are
        replaced (re-queued in simplified form) and retired from inference."""
        lhs_size = rule.lsize
        for eq in self.active:
            if eq is rule or eq.deleted:
                continue
            if eq.lsize < lhs_size and eq.rsize < lhs_size:
                continue
            hit = None
            for target_reverse in (False, True):
                side = eq.right if target_reverse else eq.left
                for path, subterm, size in _g3_positions_sized(side):
                    if size < lhs_size:
                        continue
                    sub = {}
                    if not _g3_match(rule.sl, subterm, sub):
                        continue
                    if rule.orient == 0 and not _g3_gt(subterm, _g3_subst(rule.sr, sub)):
                        continue
                    hit = (target_reverse, path)
                    break
                if hit is not None:
                    break
            if hit is None:
                continue
            new = self.make_step(rule, eq, False, hit[0], hit[1], False)
            eq.deleted = True
            if new is None:
                continue
            self.accept(new)
            if self.timed_out():
                return

    def add_active(self, eq):
        self.active.append(eq)
        self.index.add(eq.left, (eq, False))
        self.rule_log.append((eq, False))
        if eq.orient == 0:
            self.index.add(eq.right, (eq, True))
            self.rule_log.append((eq, True))
        self.version = len(self.rule_log)
        if len(self.nf_set) > self.nf_limit:
            self.nf_set = {}

    # -- inference core ---------------------------------------------------
    def make_step(self, source, target, source_reverse, target_reverse, path,
                  unify, subterm=None, size_cap=None, sub_counts=None):
        """Rewrite target's selected side at path with source.

        unify=True: ordered superposition (both renamed apart);
        unify=False: demodulation (source renamed, target kept raw).
        """
        sl = source.sr if source_reverse else source.sl
        sr = source.sl if source_reverse else source.sr
        if unify:
            tl = target.tr if target_reverse else target.tl
            tr = target.tl if target_reverse else target.tr
            if subterm is None:
                subterm = tl
                for step in path:
                    subterm = subterm[step]
            # unifiers are memoised by value: the renamed sides share their
            # variable names across equations, so equal (lhs, subterm) pairs
            # have equal (read-only) unifiers.
            key = (sl, subterm)
            cached = self.ucache.get(key)
            if cached is None:
                unifier = _g3_unify(sl, subterm)
                if len(self.ucache) > 100000:
                    self.ucache = {}
                # the instantiated-size memo is shared with the unifier
                cached = (unifier, {})
                self.ucache[key] = cached
            unifier, sizes = cached
            if unifier is None:
                return None
            scounts = source.varcounts()
            tcounts = target.varcounts()
            srx_size = _g3_counted_size(
                source.lsize if source_reverse else source.rsize,
                scounts[0] if source_reverse else scounts[1], "s", unifier, sizes)
            other_size = _g3_counted_size(
                target.lsize if target_reverse else target.rsize,
                tcounts[0] if target_reverse else tcounts[1], "t", unifier, sizes)
            if size_cap is not None:
                # cheap size-cap rejection before any term is built
                before_size = _g3_counted_size(
                    target.rsize if target_reverse else target.lsize,
                    tcounts[1] if target_reverse else tcounts[0], "t", unifier, sizes)
                if sub_counts is None:
                    sub_size = _g3_inst_size(subterm, unifier, sizes)
                else:
                    sub_size = _g3_counted_size(sub_counts[0], sub_counts[1], "t",
                                                unifier, sizes)
                if before_size - sub_size + srx_size + other_size > size_cap:
                    return None
            memo = {}
            srx = _g3_subst_m(sr, unifier, memo)
            if source.orient == 0:
                slx = _g3_subst_m(sl, unifier, memo)
                if _g3_gt(srx, slx, srx_size):
                    return None
            before = _g3_subst_m(tl, unifier, memo)
            other = _g3_subst_m(tr, unifier, memo)
            before_size = _g3_size(before)
            if target.orient == 0 and _g3_gt(other, before, other_size, before_size):
                return None
            sub_size = _g3_size(_g3_subst_m(subterm, unifier, memo))
        else:
            tl = target.right if target_reverse else target.left
            tr = target.left if target_reverse else target.right
            if subterm is None:
                subterm = tl
                for step in path:
                    subterm = subterm[step]
            unifier = {}
            if not _g3_match(sl, subterm, unifier):
                return None
            srx = _g3_subst(sr, unifier)
            srx_size = _g3_size(srx)
            if source.orient == 0 and not _g3_gt(subterm, srx, None, srx_size):
                return None
            before = tl
            other = tr
            before_size = target.rsize if target_reverse else target.lsize
            other_size = target.lsize if target_reverse else target.rsize
            sub_size = _g3_size(subterm)
        after_size = before_size - sub_size + srx_size
        if size_cap is not None and after_size + other_size > size_cap:
            return None
        after = _g3_replace(before, path, srx)
        if after == other:
            return None
        if _g3_gt(other, after, other_size, after_size):
            left, right, swapped = other, after, True
        else:
            left, right, swapped = after, other, False
        cl, cr, names = _g3_canonical(left, right)
        parents = (source, target, unifier, names, before, not unify,
                   source_reverse, target_reverse, path, swapped)
        if unify:
            recipe = ("S", source, target, source_reverse, target_reverse, path)
        else:
            recipe = ("D", source, target.recipe, source_reverse, target_reverse, path)
        return _G3Eq(cl, cr, parents, self.next_serial(),
                     max(source.depth, target.depth) + 1, len(names), recipe)

    def normalize(self, term, prefix, steps, depth=0):
        """Innermost normal form of term w.r.t. the active rules.

        Appends (path, rule, reverse, substitution, replacement) records to
        steps, in application order (inner steps first).  Normal forms are
        cached with the rule-set version at which they were established; a
        stale entry is re-validated against only the rules added since.
        Returns (term, size).
        """
        if term[0] != "o":
            return term, 1
        cached = self.nf_set.get(term)
        if cached is not None:
            size, version = cached
            if version == self.version:
                return term, size
        if depth > 200 or len(steps) > 400:
            return term, _g3_size(term)
        a, sa = self.normalize(term[1], prefix + (1,), steps, depth + 1)
        b, sb = self.normalize(term[2], prefix + (2,), steps, depth + 1)
        current = term if (a is term[1] and b is term[2]) else ("o", a, b)
        size = 1 + sa + sb
        if cached is not None and current is term and self.version - cached[1] <= 48:
            candidates = self.rule_log[cached[1]:]
        else:
            candidates = self.index.lookup(current)
        for rule, reverse in candidates:
            if rule.deleted:
                continue
            lhs = rule.sr if reverse else rule.sl
            if (rule.rsize if reverse else rule.lsize) > size:
                continue
            rhs = rule.sl if reverse else rule.sr
            sub = {}
            if not _g3_match(lhs, current, sub):
                continue
            replacement = _g3_subst(rhs, sub)
            if rule.orient == 0 and not _g3_gt(current, replacement, size):
                continue
            steps.append((prefix, rule, reverse, sub, replacement))
            return self.normalize(replacement, prefix, steps, depth + 1)
        self.nf_set[current] = (size, self.version)
        return current, size

    def demodulate(self, eq):
        """Normalise both sides of eq with active rules; returns eq or None."""
        for target_reverse in (False, True):
            side = eq.right if target_reverse else eq.left
            steps = []
            self.normalize(side, (), steps)
            for path, rule, reverse, _, _ in steps:
                new = self.make_step(rule, eq, reverse, target_reverse, path, False)
                if new is None:
                    # the rewrite makes both sides equal: eq is a tautology
                    return None
                eq = new
                if eq.left == eq.right:
                    return None
                # the rewritten side is stored on the left unless swapped;
                # if it moved, the remaining recorded paths no longer apply.
                if eq.parents[9] != target_reverse:
                    return self.demodulate(eq)
        return eq

    def neg_demodulate(self, neg):
        left, right = neg.left, neg.right
        lsteps, rsteps = list(neg.lsteps), list(neg.rsteps)
        for which in (0, 1):
            side = left if which == 0 else right
            steps = []
            self.normalize(side, (), steps)
            current = side
            for path, rule, reverse, sub, replacement in steps:
                after = _g3_replace(current, path, replacement)
                args = [sub.get(("s", i), replacement) for i in range(rule.nvars)]
                step = _G3Step(current, after, rule, args, reverse, path)
                (lsteps if which == 0 else rsteps).append(step)
                current = after
            if which == 0:
                left = current
            else:
                right = current
        if left is neg.left and right is neg.right:
            return neg
        return _G3Neg(left, right, neg.parent, neg.sigma, lsteps, rsteps, neg.serial)

    def accept(self, eq):
        """Forward simplify + dedup a freshly generated equation; push it."""
        if eq.weight > self.size_cap or eq.nvars > self.var_cap:
            return False
        eq = self.demodulate(eq)
        if eq is None or eq.left == eq.right:
            return False
        if eq.weight > self.size_cap:
            return False
        key = hash(_g3_eq_key(eq))
        if key in self.known:
            return False
        self.known.add(key)
        self.push(eq)
        self.generated += 1
        return True

    def check_neg(self, neg):
        """Demodulate a goal clause; detect refutation; push."""
        if neg.weight > self.neg_size_cap:
            return None
        neg = self.neg_demodulate(neg)
        sigma = _g3_unify(neg.left, neg.right)
        if sigma is not None:
            self.result = (neg, sigma)
            return neg
        key = _g3_key(neg.left, neg.right)
        if key in self.neg_known or len(self.neg_known) >= self.max_neg:
            return None
        self.neg_known.add(key)
        self.push_neg(neg)
        return None

    def superpose_into_neg(self, rule, neg):
        for reverse in ((False,) if rule.orient == 1 else (False, True)):
            lhs = rule.right if reverse else rule.left
            rhs = rule.left if reverse else rule.right
            for which in (0, 1):
                side = neg.left if which == 0 else neg.right
                other = neg.right if which == 0 else neg.left
                for path, subterm, _ in _g3_positions_sized(side):
                    quick = _g3_unify(lhs, subterm)
                    if quick is None:
                        continue
                    serial = self.next_serial()
                    sp = (serial, "s")
                    l2, r2 = _g3_rename(lhs, sp), _g3_rename(rhs, sp)
                    sigma = _g3_unify(l2, subterm)
                    if sigma is None:
                        continue
                    lx, rx = _g3_subst(l2, sigma), _g3_subst(r2, sigma)
                    if rule.orient == 0 and _g3_gt(rx, lx):
                        continue
                    side_x = _g3_subst(side, sigma)
                    other_x = _g3_subst(other, sigma)
                    if _g3_gt(other_x, side_x):
                        continue
                    after = _g3_replace(side_x, path, rx)
                    args = [_g3_subst(("v", (sp, i)), sigma) for i in range(rule.nvars)]
                    step = _G3Step(side_x, after, rule, args, reverse, path)
                    if which == 0:
                        new = _G3Neg(after, other_x, neg, sigma, [step], [], serial)
                    else:
                        new = _G3Neg(other_x, after, neg, sigma, [], [step], serial)
                    if self.check_neg(new) is not None:
                        return True
                    if self.timed_out():
                        return False
        return False

    def superpose(self, given, other):
        """All ordered superpositions between given and other (both roles)."""
        cap = self.size_cap
        for source, target in ((given, other), (other, given)):
            for source_reverse in ((False,) if source.orient == 1 else (False, True)):
                sr_size = source.lsize if source_reverse else source.rsize
                for target_reverse in ((False,) if target.orient == 1 else (False, True)):
                    # the conclusion is at least as large as the uninstantiated
                    # context + replacement + other side: skip hopeless positions
                    base = sr_size + (target.lsize + target.rsize)
                    for path, subterm, size, counts in target.tpos(target_reverse):
                        if base - size > cap:
                            continue
                        result = self.make_step(source, target, source_reverse,
                                                target_reverse, path, True, subterm,
                                                cap, (size, counts))
                        if result is None:
                            continue
                        self.accept(result)
                    if self.timed_out():
                        return
            if given is other:
                break

    def run(self):
        while not self.timed_out():
            if len(self.known) >= self.max_known:
                return None
            kind, given = self.pop()
            if given is None:
                break
            self.selected += 1
            if kind == 0:
                given = self.replay(given)
                if given is None:
                    continue
            if kind == 1:
                neg = self.neg_demodulate(given)
                if neg is not given:
                    sigma = _g3_unify(neg.left, neg.right)
                    if sigma is not None:
                        self.result = (neg, sigma)
                        return self.result
                    self.neg_known.add(_g3_key(neg.left, neg.right))
                self.active_neg.append(neg)
                for rule in list(self.active):
                    if self.superpose_into_neg(rule, neg):
                        return self.result
                    if self.timed_out():
                        return None
                continue
            eq = self.demodulate(given)
            if eq is None or eq.left == eq.right:
                continue
            if eq is not given:
                key = hash(_g3_eq_key(eq))
                if key in self.known:
                    continue
                self.known.add(key)
            self.add_active(eq)
            if eq.orient == 1:
                self.backward_simplify(eq)
                if self.timed_out():
                    return None
            for neg in list(self.active_neg):
                if self.superpose_into_neg(eq, neg):
                    return self.result
                if self.timed_out():
                    return None
            for other in list(self.active):
                if other.deleted:
                    continue
                self.superpose(eq, other)
                if self.timed_out():
                    return None
            if self.selected % 50 == 0:
                self.active = [e for e in self.active if not e.deleted]
        return None


def _g3_flatten(neg, sigma, default):
    chain = []
    node = neg
    while node is not None:
        chain.append(node)
        node = node.parent
    chain.reverse()
    lsteps, rsteps = [], []
    for node in chain:
        if node.sigma:
            for step in lsteps + rsteps:
                step.before = _g3_subst(step.before, node.sigma)
                step.after = _g3_subst(step.after, node.sigma)
                step.args = [_g3_subst(a, node.sigma) for a in step.args]
        for s in node.lsteps:
            lsteps.append(_G3Step(s.before, s.after, s.equation, list(s.args), s.reverse, s.path))
        for s in node.rsteps:
            rsteps.append(_G3Step(s.before, s.after, s.equation, list(s.args), s.reverse, s.path))
    # final unifier + default for leftover variables
    def finish(term):
        term = _g3_subst(term, sigma)

        def visit(t):
            if t[0] == "v":
                return default
            if t[0] != "o":
                return t
            return ("o", visit(t[1]), visit(t[2]))

        return visit(term)

    for step in lsteps + rsteps:
        step.before = finish(step.before)
        step.after = finish(step.after)
        step.args = [finish(a) for a in step.args]
    return lsteps, rsteps


def _g3_dependencies(roots):
    result = []
    seen = set()

    def visit(equation):
        if equation.serial in seen:
            return
        seen.add(equation.serial)
        if equation.parents[0] != "h":
            visit(equation.parents[0])
            visit(equation.parents[1])
        result.append(equation)

    for equation in roots:
        visit(equation)
    return result


def _g3_emit(goal_vars, lsteps, rsteps, robust=False):
    roots = [step.equation for step in lsteps + rsteps]
    dependencies = _g3_dependencies(roots)
    names = {equation.serial: "e" + str(i) for i, equation in enumerate(dependencies)}
    lines = ["import JudgeProblem", "", "def submission : Goal := by", "  intro G _ h"]

    def close(term):
        if robust:
            return "first | exact " + term + " | grind"
        return "exact " + term

    for equation in dependencies:
        name = names[equation.serial]
        variables = sorted(_g3_vars(equation.left) | _g3_vars(equation.right))
        binders = " ".join("X" + str(v) for v in variables)
        lines.append("  have " + name + " (" + binders + " : G) : "
                     + _g3_lean(equation.left) + " = " + _g3_lean(equation.right) + " := by")
        if equation.parents[0] == "h":
            reverse = equation.parents[1]
            h_args = equation.parents[2]
            app = "h" + (" " + " ".join("X" + str(v) for v in h_args) if h_args else "")
            lines.append("    exact " + ("(" + app + ").symm" if reverse else app))
            continue
        (source, target, _, _, _, _, source_reverse,
         target_reverse, path, swapped) = equation.parents
        source_args, target_args, before = equation.step_args()
        source_app = _g3_application(names[source.serial], source_args, source_reverse)
        target_app = _g3_application(names[target.serial], target_args, target_reverse)
        context = _g3_context_lean(before, path)
        congr = "congrArg (fun q => " + context + ") (" + source_app + ")"
        proof = "(" + congr + ").symm.trans (" + target_app + ")"
        if swapped:
            proof = "(" + proof + ").symm"
        lines.append("    " + close(proof))

    if goal_vars:
        lines.append("  intro " + " ".join(goal_vars))
    step_names = []
    for index, step in enumerate(lsteps + rsteps):
        name = "g" + str(index)
        step_names.append(name)
        lines.append("  have " + name + " : " + _g3_lean(step.before) + " = "
                     + _g3_lean(step.after) + " := by")
        app = _g3_application(names[step.equation.serial], step.args, step.reverse)
        if step.path:
            app = "congrArg (fun q => " + _g3_context_lean(step.before, step.path) + ") (" + app + ")"
        lines.append("    " + close(app))
    left_names = step_names[:len(lsteps)]
    right_names = step_names[len(lsteps):]

    def chain(ns):
        if not ns:
            return "rfl"
        result = ns[0]
        for n in ns[1:]:
            result = "(" + result + ").trans " + n
        return result

    if not lsteps and not rsteps:
        final = "rfl"
    elif not rsteps:
        final = chain(left_names)
    elif not lsteps:
        final = "(" + chain(right_names) + ").symm"
    else:
        final = "(" + chain(left_names) + ").trans (" + chain(right_names) + ").symm"
    if robust:
        lines.append("  first | exact " + final + " | grind")
    else:
        lines.append("  exact " + final)
    return "\n".join(lines) + "\n"


_G3_LAST = {"proof": None, "prover": None}


def _g3_emit_pool(prover, max_lemmas=40, max_weight=40):
    """Certificate from the smallest derived lemmas plus a final `grind`."""
    pool = [eq for eq in prover.active
            if eq.parents[0] != "h" and eq.weight <= max_weight]
    pool.sort(key=lambda e: (e.weight, e.nvars, e.serial))
    pool = pool[:max_lemmas]
    if not pool:
        return None
    dependencies = _g3_dependencies(pool)
    names = {equation.serial: "e" + str(i) for i, equation in enumerate(dependencies)}
    lines = ["import JudgeProblem", "", "def submission : Goal := by", "  intro G _ h"]
    for equation in dependencies:
        name = names[equation.serial]
        variables = sorted(_g3_vars(equation.left) | _g3_vars(equation.right))
        binders = " ".join("X" + str(v) for v in variables)
        lines.append("  have " + name + " (" + binders + " : G) : "
                     + _g3_lean(equation.left) + " = " + _g3_lean(equation.right) + " := by")
        if equation.parents[0] == "h":
            reverse = equation.parents[1]
            h_args = equation.parents[2]
            app = "h" + (" " + " ".join("X" + str(v) for v in h_args) if h_args else "")
            lines.append("    exact " + ("(" + app + ").symm" if reverse else app))
            continue
        (source, target, _, _, _, _, source_reverse,
         target_reverse, path, swapped) = equation.parents
        source_args, target_args, before = equation.step_args()
        source_app = _g3_application(names[source.serial], source_args, source_reverse)
        target_app = _g3_application(names[target.serial], target_args, target_reverse)
        context = _g3_context_lean(before, path)
        congr = "congrArg (fun q => " + context + ") (" + source_app + ")"
        proof = "(" + congr + ").symm.trans (" + target_app + ")"
        if swapped:
            proof = "(" + proof + ").symm"
        lines.append("    exact " + proof)
    if prover.goal_vars:
        lines.append("  intro " + " ".join(prover.goal_vars))
    lines.append("  grind")
    return "\n".join(lines) + "\n"


def g3_pool_cert(max_lemmas=40, max_weight=40):
    """Lemma-pool + grind certificate from the last (failed) g3 search."""
    prover = _G3_LAST.get("prover")
    if prover is None:
        return None
    try:
        return _g3_emit_pool(prover, max_lemmas, max_weight)
    except Exception:
        return None


def g3_reemit(robust=True):
    """Re-emit the last successful g3 proof (robust form: grind fallbacks)."""
    proof = _G3_LAST.get("proof")
    if proof is None:
        return None
    goal_vars, lsteps, rsteps = proof
    return _g3_emit(goal_vars, lsteps, rsteps, robust=robust)


def g3_prove(eq1_text, eq2_text, time_budget_s=300.0, rounds=None, robust=False,
             stats=None, max_known=250000, age_ratio=6, var_penalty=2, var_cap=10,
             collapse_bonus=0, rhs_factor=1):
    """Proof-producing ordered superposition; returns a Lean certificate or None."""
    try:
        hypothesis = _G3Parser(eq1_text).equation()
        goal = _G3Parser(eq2_text).equation()
    except (_G3ParseError, TypeError, ValueError):
        return None
    budget = max(0.05, float(time_budget_s))
    start = time.monotonic()
    end = start + budget
    if rounds is None:
        # Iterative size-cap deepening.  A round that saturates (its capped
        # passive queue runs empty) hands its remaining time to the next one;
        # the last rounds relax the caps and switch to the Vampire-like
        # selection (no variable penalty, age ratio 2) for diversity.  If
        # every listed round saturates with time left, the caps keep growing.
        rounds = [(24, 0.06), (32, 0.12), (44, 0.25), (60, 0.55),
                  (80, 0.8, {"var_penalty": 1, "age_ratio": 4}),
                  (120, 1.0, {"var_penalty": 0, "age_ratio": 2, "var_cap": var_cap + 2})]
    _G3_LAST["proof"] = None
    best_prover = None
    queue = list(rounds)
    index = 0
    while index < len(queue):
        entry = queue[index]
        index += 1
        size_cap, fraction = entry[0], entry[1]
        overrides = entry[2] if len(entry) > 2 else {}
        now = time.monotonic()
        if now >= end:
            break
        deadline = min(end, start + fraction * budget) if fraction < 1.0 else end
        if deadline <= now:
            continue
        options = {"max_known": max_known, "age_ratio": age_ratio,
                   "var_penalty": var_penalty, "var_cap": var_cap,
                   "collapse_bonus": collapse_bonus, "rhs_factor": rhs_factor}
        options.update(overrides)
        if size_cap > 60:
            # memory scales with clauses x clause size: shrink the clause
            # budget for the relaxed-cap rounds
            options["max_known"] = max(20000, int(options["max_known"] * 60 / size_cap))
        prover = _G3Prover(hypothesis, goal, deadline, size_cap=size_cap, **options)
        try:
            result = prover.run()
        except (RecursionError, MemoryError):
            result = None
        saturated = not prover.queue and result is None
        if stats is not None:
            stats.append({"size_cap": size_cap, "selected": prover.selected,
                          "generated": prover.generated, "known": len(prover.known),
                          "neg": len(prover.neg_known), "found": result is not None,
                          "secs": round(time.monotonic() - now, 1),
                          "saturated": saturated})
        if best_prover is None or len(prover.active) >= len(best_prover.active):
            best_prover = prover
        if result is not None:
            neg, sigma = result
            default = ("k", prover.goal_vars[0]) if prover.goal_vars else prover.goal[0]
            lsteps, rsteps = _g3_flatten(neg, sigma, default)
            _G3_LAST["proof"] = (prover.goal_vars, lsteps, rsteps)
            _G3_LAST["prover"] = prover
            return _g3_emit(prover.goal_vars, lsteps, rsteps, robust=robust)
        if index == len(queue) and saturated and size_cap < 400:
            # the capped search space is exhausted: relax the caps and go on
            queue.append((size_cap + 40, 1.0,
                          dict(overrides, var_cap=options["var_cap"] + 2)))
    _G3_LAST["prover"] = best_prover
    return None


def general_true_cert(eq1_text, eq2_text, time_budget_s=30.0, quick=False):
    """Return a complete Lean certificate for eq1 => eq2, or ``None``.

    Runs the G3 ordered-superposition prover (anytime: iterative size caps)
    for most of the budget; the older goal-joining prover (_g2) gets the
    remaining slice as a diversity fallback.
    """
    try:
        budget = max(0.01, float(time_budget_s))
    except (TypeError, ValueError):
        return None
    start = time.monotonic()
    g3_budget = budget if quick else budget * 0.85
    try:
        cert = g3_prove(eq1_text, eq2_text, time_budget_s=g3_budget)
    except Exception:
        cert = None
    if cert is not None:
        return cert
    remaining = budget - (time.monotonic() - start)
    if quick or remaining < 0.5:
        return None
    try:
        hypothesis = _G2Parser(eq1_text).equation()
        goal = _G2Parser(eq2_text).equation()
    except (_G2ParseError, TypeError, ValueError):
        return None
    try:
        joined = _g2_search(hypothesis, goal, time.monotonic() + remaining)
    except Exception:
        joined = None
    if joined is None:
        return None
    return _g2_emit(goal, joined)


def general_true_cert_robust():
    """Robust re-emission (per-step `grind` fallbacks) of the last G3 proof."""
    try:
        return g3_reemit(robust=True)
    except Exception:
        return None


def general_true_pool_cert():
    """Lemma-pool + `grind` certificate from the last failed G3 search."""
    try:
        return g3_pool_cert()
    except Exception:
        return None


def main():
    startup = read_message()
    problem = startup["problem"]
    eq1_text, eq2_text = problem["equation1"], problem["equation2"]
    try:
        wall_budget = float((startup.get("budget") or {}).get("timeout_seconds", 3600))
    except (TypeError, ValueError):
        wall_budget = 3600.0
    if not (wall_budget > 0):
        wall_budget = 3600.0
    # True-side deterministic budgets scale with the per-problem wall clock
    # (Solo 3600 s -> 600 s deep search; Marathon-style 300 s -> 60 s).
    deep_true_budget = min(600.0, max(20.0, wall_budget / 6.0))
    quick_true_budget = min(6.0, max(1.0, wall_budget / 600.0))

    # Stages are ordered cheapest-first so the common cases resolve in
    # milliseconds and only the genuine residuals pay the expensive searches.

    # Stage 1: cheap finite-magma counterexample (false) — brute Fin 2-3, F_p
    # linear, F_2^2 matrix, Z_n polynomial, then the Fin-n arithmetic families
    # (linear/affine mod n <= 50, F_3^2 / F_2^3 matrix-linear) and the canned
    # Austin-pair ℕ models. No model finder yet.
    found = search_counterexample(eq1_text, eq2_text, use_linear=True,
                                  use_model_finder=False)
    if found is not None:
        result = call_judge("false", make_false_code(problem, found))
        if result.get("status") == "accepted":
            return

    # Stage 2: cheap true proofs — singleton (x = x-free) and substitution-instance.
    proof = singleton_true_proof(eq1_text, eq2_text)
    if proof is not None:
        result = call_judge("true", make_true_code(problem, proof))
        if result.get("status") == "accepted":
            return

    proof = substitution_instance_true_proof(eq1_text, eq2_text)
    if proof is not None:
        result = call_judge("true", make_true_code(problem, proof))
        if result.get("status") == "accepted":
            return

    # Stage 2b: singleton-forced true proof (deterministic superposition) — fast
    # when it applies (a collapse identity is found in milliseconds); returns None
    # otherwise. Placed before the model finder because singleton hypotheses close
    # here instantly.
    cert = singleton_forced_cert(eq1_text, eq2_text, time_budget_s=8.0)
    if cert is not None:
        result = call_judge("true", cert)
        if result.get("status") == "accepted":
            return

    # Stage 2c: quick pass of the general superposition prover (true). It
    # settles almost every provable implication in well under a second, so
    # it runs before the model finder; the deep anytime pass comes later.
    cert = general_true_cert(eq1_text, eq2_text, time_budget_s=quick_true_budget,
                             quick=True)
    if cert is not None:
        result = call_judge("true", cert)
        if result.get("status") == "accepted":
            return
        cert = general_true_cert_robust()
        if cert is not None:
            result = call_judge("true", cert)
            if result.get("status") == "accepted":
                return

    # Stage 3: systematic SEM finite-model search (false) for irregular carriers
    # 4..10 — the first expensive stage (bounded budget).
    found = search_counterexample(eq1_text, eq2_text, use_linear=False,
                                  use_structured=False, use_austin=False,
                                  use_model_finder=True, model_finder_budget_s=8.0)
    if found is not None:
        result = call_judge("false", make_false_code(problem, found))
        if result.get("status") == "accepted":
            return

    # Stage 4: deep false search — heavier structured families (quadratic grid
    # n=7..8, F_5^2, sampled polynomial ops up to n=16) and a long model-finder
    # run over carriers 4..10. Only problems every cheaper stage missed pay this.
    found = search_counterexample(eq1_text, eq2_text, use_linear=False,
                                  use_structured=False, use_austin=False,
                                  use_deep=True, deep_budget_s=60.0,
                                  use_model_finder=True, model_finder_budget_s=120.0)
    if found is not None:
        result = call_judge("false", make_false_code(problem, found))
        if result.get("status") == "accepted":
            return

    # Stage 5: deep anytime pass of the general superposition prover (true):
    # ordered (KBO) unit superposition with demodulation, negated-goal
    # paramodulation and iterative size-cap deepening, replayed as an exact
    # have/congrArg certificate. Most expensive deterministic stage.
    cert = general_true_cert(eq1_text, eq2_text, time_budget_s=deep_true_budget)
    if cert is not None:
        result = call_judge("true", cert)
        if result.get("status") == "accepted":
            return
        cert = general_true_cert_robust()
        if cert is not None:
            result = call_judge("true", cert)
            if result.get("status") == "accepted":
                return
    else:
        # Stage 5b: lemma pool + `grind` -- the smallest derived consequences
        # of the failed search as exact lemmas, then grind closes the goal.
        cert = general_true_pool_cert()
        if cert is not None:
            result = call_judge("true", cert)
            if result.get("status") == "accepted":
                return

    # Pass 3: gpt-oss-120b fallback via the organizer proxy. The solver sends a
    # context dict (the proxy fills the PROMPT template and calls the model);
    # we parse the JSON verdict, build the Lean cert with the floor's helpers,
    # and iterate on judge feedback until the budget is spent.
    hint = deterministic_hint(eq1_text, eq2_text)
    for rnd in range(MAX_LLM_ROUNDS):
        llm_result = call_llm({"hint": hint, "round": str(rnd)})
        if "error" in llm_result:
            break
        answer = extract_json(llm_result.get("response", ""))
        if not isinstance(answer, dict):
            continue
        verdict = answer.get("verdict")
        if verdict == "true":
            body = clean_proof_body(answer.get("proof", "") or "")
            if not body:
                continue
            result = call_judge("true", make_true_code(problem, body))
            if result.get("status") == "accepted":
                return
        elif verdict == "false":
            tbl = answer.get("counterexample_table")
            if not valid_llm_table(tbl):
                continue
            result = call_judge("false", make_false_code(problem, {"n": len(tbl), "table": tbl}))
            if result.get("status") == "accepted":
                return
        # Rejections are surfaced to the next round via {history.attempts}.


if __name__ == "__main__":
    main()
