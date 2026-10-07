# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Fail-closed tests for the exact target."""
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
from rh_official_target_gate import GOAL, classify

SOURCE = """import FormalConjecturesUtil
namespace RiemannHypothesis
theorem riemannHypothesis : RiemannHypothesis := by
  apply AEGIS.RHRestrictedWeilCriterionV13.restricted_weil_criterion_v13
end RiemannHypothesis
namespace GRH
theorem generalized_riemann_hypothesis : False := by
  sorry
end GRH
"""
EXPECTED = f"""FormalConjectures/Millennium/RiemannHypothesis.lean:59:49: error: unsolved goals
⊢ {GOAL}
FormalConjectures/Millennium/RiemannHypothesis.lean:81:8: warning: declaration uses sorry
"""

class TargetGateTests(unittest.TestCase):
    def test_exact_residual_is_open_not_success(self):
        self.assertEqual(classify(SOURCE, EXPECTED, 1)[0], "OPEN_UNIVERSAL_ZERO_QUADRATIC")
    def test_correct_residual_with_additional_error_fails(self):
        self.assertEqual(classify(SOURCE, EXPECTED + "error: unknown identifier x\n", 1)[0], "COMPILER_FAILURE_UNEXPECTED")
    def test_different_residual_fails(self):
        self.assertEqual(classify(SOURCE, EXPECTED.replace(GOAL, "True"), 1)[0], "COMPILER_FAILURE_UNEXPECTED")
    def test_two_goals_fail(self):
        self.assertEqual(classify(SOURCE, EXPECTED + f"⊢ {GOAL}\n", 1)[0], "COMPILER_FAILURE_UNEXPECTED")
    def test_success_without_ax_check_not_promoted(self):
        self.assertEqual(classify(SOURCE, "GRH warning: sorry", 0)[0], "COMPILED_AWAITING_AXIOM_AUDIT")
    def test_standard_axioms_closed(self):
        self.assertEqual(classify(SOURCE, "", 0, "'RiemannHypothesis.riemannHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]")[0], "FORMAL_RH_CLOSED")
    def test_extra_axiom_rejected(self):
        self.assertEqual(classify(SOURCE, "", 0, "'RiemannHypothesis.riemannHypothesis' depends on axioms: [propext, AEGIS.rh_ax]")[0], "AXIOM_AUDIT_FAILED")
    def test_sorryax_rejected(self):
        self.assertEqual(classify(SOURCE, "", 0, "'RiemannHypothesis.riemannHypothesis' depends on axioms: [sorryAx]")[0], "AXIOM_AUDIT_FAILED")
    def test_missing_axiom_probe_rejected(self):
        self.assertEqual(classify(SOURCE, "", 0, "")[0], "AXIOM_AUDIT_MISSING")
    def test_placeholder_in_rh_rejected(self):
        source = SOURCE.replace("  apply AEGIS.RHRestrictedWeilCriterionV13.restricted_weil_criterion_v13", "  sorry")
        self.assertEqual(classify(source, "", 0)[0], "TARGET_SOURCE_INVALID")
    def test_grh_sorry_not_rh_placeholder(self):
        self.assertEqual(classify(SOURCE, EXPECTED, 1)[0], "OPEN_UNIVERSAL_ZERO_QUADRATIC")
    def test_success_with_compiler_error_rejected(self):
        self.assertEqual(classify(SOURCE, "error: unknown identifier x", 0)[0], "COMPILER_OUTPUT_INVALID")

if __name__ == "__main__":
    unittest.main()
