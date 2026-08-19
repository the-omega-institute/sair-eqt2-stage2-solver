#!/usr/bin/env python3
"""Offline (no judge) checks for the extended FALSE side of submission/solver.py.

Run: python3 tests/test_false_side_v2.py
"""
import importlib.util
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
SOLVER = os.path.join(HERE, "..", "submission", "solver.py")
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("solver_under_test", SOLVER)
S = importlib.util.module_from_spec(spec)
spec.loader.exec_module(S)

RESIDUALS = [
    ("hard2_0027", "x = y ◇ ((z ◇ (y ◇ y)) ◇ x)", "x = (y ◇ z) ◇ ((x ◇ z) ◇ x)", "austin_nat"),
    ("hard2_0051", "x = (y ◇ ((y ◇ x) ◇ x)) ◇ y", "x ◇ (x ◇ y) = z ◇ (z ◇ y)", "linear_n"),
    ("hard1_0062", "x = ((y ◇ x) ◇ z) ◇ (z ◇ y)", "x = (y ◇ (y ◇ (x ◇ x))) ◇ x", "vec_linear_2_3"),
]


def check_table_witness(eq1, eq2, found):
    n = found["n"]
    table = found.get("table")
    if table is None:
        if "coeffs" in found:
            table = S._poly_table(n, found["coeffs"])
        elif "c" in found:
            table = S.affine_table(n, found["a"], found["b"], found["c"])
        else:
            table = S.linear_table(n, found["a"], found["b"])
    op = S.table_to_op(table)
    assert S.equation_holds(S.parse_equation(eq1), n, op)
    assert S.equation_fails(S.parse_equation(eq2), n, op)


def main():
    # 1. residuals are found by the deterministic floor (stage 1)
    for pid, eq1, eq2, stage in RESIDUALS:
        t = time.time()
        found = S.search_counterexample(eq1, eq2, use_linear=True, use_model_finder=False)
        assert found is not None, pid
        assert found["stage"] == stage, (pid, found["stage"])
        if found.get("carrier") != "nat":
            check_table_witness(eq1, eq2, found)
        code = S.make_false_code({}, found)
        assert "sorry" not in code and len(code.encode()) < 10000
        print("ok", pid, found["stage"], found.get("n"), round(time.time() - t, 2), "s")

    # 2. Latin inference flags
    assert S._mf_latin_flags(S.parse_equation("x = ((y ◇ x) ◇ z) ◇ (z ◇ y)")) == (True, True)
    assert S._mf_latin_flags(S.parse_equation("x = (x ◇ y) ◇ ((y ◇ y) ◇ z)")) == (False, True)
    assert S._mf_latin_flags(S.parse_equation("x ◇ (x ◇ y) = z ◇ (z ◇ y)")) == (False, False)

    # 3. model finder finds the Fin 8 quasigroup for hard1_0062 quickly
    t = time.time()
    mf = S.find_countermodel(RESIDUALS[2][1], RESIDUALS[2][2], max_n=10, time_budget_s=30.0)
    assert mf is not None and mf[0] == 8, mf
    check_table_witness(RESIDUALS[2][1], RESIDUALS[2][2], {"n": mf[0], "table": mf[1]})
    print("ok model finder Fin 8 in", round(time.time() - t, 2), "s")

    # 4. Austin canned laws match up to renaming
    for text in ("x = (y ◇ (z ◇ z)) ◇ (z ◇ x)", "y = (y ◇ z) ◇ ((z ◇ z) ◇ x)"):
        assert S.austin_counterexample(text, "x = y") is not None, text
    assert S.austin_counterexample("x = (y ◇ (z ◇ z)) ◇ (z ◇ x)", "x = (y ◇ (z ◇ z)) ◇ (z ◇ x)") is None

    # 5. emitter shapes
    code = S.make_false_code({}, {"n": 13, "lean_op": "(7 * x.val + 7 * y.val) % 13"})
    assert "def op (x y : Fin 13)" in code and "decideFin!" in code
    code = S.make_false_code({}, {"n": 11, "table": [[(i * j) % 11 for j in range(11)] for i in range(11)]})
    assert "def tbl : Nat :=" in code
    code = S.make_false_code({}, {"n": 5, "a": 2, "b": 3})
    assert "finOpTable" in code
    print("all checks passed")


if __name__ == "__main__":
    main()
