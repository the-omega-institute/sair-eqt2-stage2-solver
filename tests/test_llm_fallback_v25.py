#!/usr/bin/env python3
"""Offline checks for the v2.5 LLM fallback helpers."""

import importlib.util
import unittest
from pathlib import Path


SOLVER = Path(__file__).resolve().parents[1] / "submission" / "solver.py"
spec = importlib.util.spec_from_file_location("solver_v25", SOLVER)
solver = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(solver)


class TestLlmFallbackV25(unittest.TestCase):
    def test_operator_normalization_for_body_and_raw_code(self):
        self.assertEqual(solver.clean_proof_body("exact h x * y"), "exact h x ◇ y")
        code, error = solver.validate_llm_code(
            "true", "import JudgeProblem\ndef submission : Goal := by\n  exact h * x"
        )
        self.assertIsNone(error)
        self.assertIn("h ◇ x", code)

    def test_raw_code_accept_reject_paths_and_caps(self):
        good, error = solver.validate_llm_code(
            "false", "import JudgeProblem\ndef submission : Goal := by\n  decide"
        )
        self.assertIsNone(error)
        self.assertIsNotNone(good)

        for bad in (
            "import JudgeProblem\ndef helper : Goal := by decide",
            "import JudgeProblem\ndef submission : Goal := by\n  sorry",
        ):
            code, error = solver.validate_llm_code("true", bad)
            self.assertIsNone(code)
            self.assertTrue(error)

        code, error = solver.validate_llm_code(
            "true", "import JudgeProblem\ndef submission : Goal := by\n  decide", 20
        )
        self.assertIsNone(code)
        self.assertIn("exceeds", error)

        code, error = solver.validate_llm_code(
            "false", "import JudgeProblem\ndef submission : Goal := by\n  " + "x" * 80,
            100000, 50,
        )
        self.assertIsNone(code)
        self.assertIn("false raw certificate", error)

    def test_hint_completion_and_timeout_branches(self):
        complete = solver.deterministic_hint("x = y", "x = y", False)
        timeout = solver.deterministic_hint("x = y", "x = y", True)
        self.assertIn("Search completed without a countermodel", complete)
        self.assertIn("Search hit its time budget", timeout)
        self.assertIn("inconclusive", timeout)
        self.assertIn("order >= 9", timeout)
        self.assertIn("infinite model", timeout)
        self.assertNotIn("very likely TRUE", timeout)

    def test_round_direction_alternates_for_both_preferences(self):
        self.assertEqual(
            [solver.llm_round_direction(i, "true") for i in range(4)],
            ["true", "false", "true", "false"],
        )
        self.assertEqual(
            [solver.llm_round_direction(i, "false") for i in range(4)],
            ["false", "true", "false", "true"],
        )
        self.assertIn("Round 1", solver.llm_round_instruction(0, "false"))
        self.assertIn("verdict FALSE", solver.llm_round_instruction(0, "false"))


if __name__ == "__main__":
    unittest.main()
