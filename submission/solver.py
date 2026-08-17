#!/usr/bin/env python3
"""Solo solver for SAIR-EQT2 Stage 2 — deterministic floor + gpt-oss-120b fallback.

Single-file, official stdin/stdout JSON protocol. Three escalating passes:

  Pass 1 (deterministic, no LLM): finite-magma counterexample for the false branch
    (brute Fin 2-3, then F_p linear p<=7, then F_2^2/Fin 4 matrix-linear, all via
    finOpTable).
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
        self.table[cell] = value
        self.assign_trail.append(cell)
        if not self._least_number_ok():
            return False
        self._schedule_cell(cell)
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
        while len(self.assign_trail) > assign_mark:
            self.table[self.assign_trail.pop()] = UNKNOWN

    def _choose_cell(self):
        if self.goal_first:
            goal_cells = [cell for cell in self.dependencies[-1]
                          if self.table[cell] == UNKNOWN]
            if goal_cells:
                return max(goal_cells,
                           key=lambda cell: (len(self.watchers[cell]), -cell))
        best = None
        best_score = -1
        for cell, value in enumerate(self.table):
            if value == UNKNOWN:
                score = len(self.watchers[cell])
                if score > best_score:
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


# affine stage disabled by default: empirically +0 on normal+hard1/2/3 samples
# (with no constants in the input language, nonzero affine offsets are
# equationally equivalent to linear), and it costs up to AFFINE_CANDIDATE_LIMIT
# evals/problem. Kept for reference; flip use_affine=True to re-enable.
def search_counterexample(eq1_text, eq2_text, use_linear=True, use_affine=False,
                          use_model_finder=True, model_finder_budget_s=8.0):
    eq1 = parse_equation(eq1_text)
    eq2 = parse_equation(eq2_text)
    found = brute_counterexample(eq1, eq2, max_n=3)
    if found is not None:
        return found
    if use_linear:
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


def make_false_code(problem, cex):
    n = cex["n"]
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


def general_true_cert(eq1_text, eq2_text, time_budget_s=30.0):
    """Return a complete Lean certificate for eq1 => eq2, or ``None``."""
    try:
        hypothesis = _G2Parser(eq1_text).equation()
        goal = _G2Parser(eq2_text).equation()
        budget = max(0.01, float(time_budget_s))
    except (_G2ParseError, TypeError, ValueError):
        return None
    joined = _g2_search(hypothesis, goal, time.monotonic() + budget)
    if joined is None:
        return None
    return _g2_emit(goal, joined)


def main():
    startup = read_message()
    problem = startup["problem"]
    eq1_text, eq2_text = problem["equation1"], problem["equation2"]

    # Stages are ordered cheapest-first so the common cases resolve in
    # milliseconds and only the genuine residuals pay the expensive searches.

    # Stage 1: cheap finite-magma counterexample (false) — brute Fin 2-3, F_p
    # linear, F_2^2 matrix, Z_n polynomial. No model finder yet.
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

    # Stage 3: systematic SEM finite-model search (false) for irregular carriers
    # 4..8 — the first expensive stage (bounded budget).
    found = search_counterexample(eq1_text, eq2_text, use_linear=False,
                                  use_model_finder=True, model_finder_budget_s=8.0)
    if found is not None:
        result = call_judge("false", make_false_code(problem, found))
        if result.get("status") == "accepted":
            return

    # Stage 4: general goal-directed superposition prover for non-singleton true
    # implications (goal proved directly by equational joining). Most expensive
    # deterministic stage.
    cert = general_true_cert(eq1_text, eq2_text, time_budget_s=30.0)
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
