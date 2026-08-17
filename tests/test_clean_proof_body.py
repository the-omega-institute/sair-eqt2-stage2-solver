#!/usr/bin/env python3
"""Unit tests for clean_proof_body intro-G stripping (solver scaffolding only)."""

from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path


def _load_clean_proof_body():
    path = Path(__file__).resolve().parents[1] / "submission" / "solver.py"
    spec = importlib.util.spec_from_file_location("competition_solver", path)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod.clean_proof_body


clean_proof_body = _load_clean_proof_body()


class TestCleanProofBody(unittest.TestCase):
    def test_strips_leading_intro_g(self):
        body = "intro G _ h\nsimpa using h x ((x ◇ x) ◇ x) x x"
        self.assertEqual(
            clean_proof_body(body),
            "simpa using h x ((x ◇ x) ◇ x) x x",
        )

    def test_preserves_body_without_intro_g(self):
        body = "simpa using h x ((x ◇ x) ◇ x) x x"
        self.assertEqual(clean_proof_body(body), body)

    def test_preserves_intro_x_only(self):
        body = "intro x\nsimpa using h x ((x ◇ x) ◇ x) x x"
        self.assertEqual(clean_proof_body(body), body)

    def test_strips_after_by_prefix(self):
        body = (
            "by\n"
            "  intro G _ h\n"
            "  intro x\n"
            "  simpa using h x ((x ◇ x) ◇ x) x x"
        )
        self.assertEqual(
            clean_proof_body(body),
            "intro x\n  simpa using h x ((x ◇ x) ◇ x) x x",
        )

    def test_strips_after_assign_by_prefix(self):
        body = "def submission : Goal := by\nintro G _ h\nexact h"
        self.assertEqual(clean_proof_body(body), "exact h")

    def test_whitespace_variants_of_intro_g(self):
        cases = [
            "intro  G  _  h\nexact h",
            "intro\tG\t_\th\nexact h",
            "  intro G _ h  \nexact h",
            "intro G _ h\n\nexact h",
        ]
        for body in cases:
            with self.subTest(body=body):
                self.assertEqual(clean_proof_body(body), "exact h")

    def test_does_not_strip_mid_body_intro_g(self):
        body = "intro x\nintro G _ h\nexact h"
        self.assertEqual(clean_proof_body(body), body)

    def test_does_not_strip_intro_g_with_extra_binder(self):
        body = "intro G _ h x\nexact h"
        self.assertEqual(clean_proof_body(body), body)


if __name__ == "__main__":
    unittest.main()
