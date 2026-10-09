import Mathlib.Tactic

/-!
AEGIS Omega -- complete four-block comparison certificate V2.

The earlier 9/8 number tests equal coefficients after deleting the farthest
pair. It is NOT an all-coefficient PSD or Gershgorin threshold.

This file includes all six pairs. The comparison constants are
51/100 (adjacent), 9/25 (next-neighbour), and 13/50 (farthest).
The last number is an EXPLICIT proposed analytic premise, not a derived
bound on the actual Weil form. The exact sum-of-squares identity proves a
158/125 comparison bound for arbitrary real coefficients. A 32/25 diagonal
then leaves 2/125 of coercivity. No assertion of global Weil sign or RH.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFourBlockComparisonV2

def energy4 (x0 x1 x2 x3 : ℝ) : ℝ :=
  x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2

def cross4 (a b r x0 x1 x2 x3 : ℝ) : ℝ :=
  2 * (a * (x0 * x1 + x1 * x2 + x2 * x3) +
       b * (x0 * x2 + x1 * x3) + r * x0 * x3)

/-- Exact reversal-even / reversal-odd decomposition; the farthest pair r
is retained. This is an identity, not an assumption of sign. -/
theorem sector_decomposition_v2 (d a b r x0 x1 x2 x3 : ℝ) :
    2 * (d * energy4 x0 x1 x2 x3 - cross4 a b r x0 x1 x2 x3) =
      (d - r) * (x0 + x3) ^ 2 + (d - a) * (x1 + x2) ^ 2 -
        2 * (a + b) * (x0 + x3) * (x1 + x2) +
      (d + r) * (x0 - x3) ^ 2 + (d + a) * (x1 - x2) ^ 2 -
        2 * (a - b) * (x0 - x3) * (x1 - x2) := by
  unfold energy4 cross4
  ring

/-- Regression witness: 9/8 fails even when the farthest entry is zero. -/
theorem nine_eighths_counterexample_v2 :
    (9 / 8 : ℝ) * energy4 4 5 5 4 -
      cross4 (51 / 100) (9 / 25) 0 4 5 5 4 = -(57 / 20 : ℝ) := by
  norm_num [energy4, cross4]

theorem nine_eighths_not_universal_v2 :
    ¬ (∀ x0 x1 x2 x3 : ℝ,
      cross4 (51 / 100) (9 / 25) 0 x0 x1 x2 x3 ≤
        (9 / 8 : ℝ) * energy4 x0 x1 x2 x3) := by
  intro h
  have hbad := h 4 5 5 4
  norm_num [energy4, cross4] at hbad

def comparisonSOS (x0 x1 x2 x3 : ℝ) : ℝ :=
  (17 / 6500 : ℝ) * ((15 * x0 - 13 * x1) ^ 2 + (13 * x2 - 15 * x3) ^ 2) +
  (3 / 1625 : ℝ) * ((15 * x0 - 13 * x2) ^ 2 + (13 * x1 - 15 * x3) ^ 2) +
  (51 / 100 : ℝ) * (x1 - x2) ^ 2 +
  (13 / 50 : ℝ) * (x0 - x3) ^ 2 +
  (1 / 6500 : ℝ) * (x0 ^ 2 + x3 ^ 2)

/-- Rational weighted-Laplacian certificate with weights (13,15,15,13).
It verifies all coefficients, rather than sampling vectors/eigenvalues. -/
theorem comparison_sos_identity_v2 (x0 x1 x2 x3 : ℝ) :
    (158 / 125 : ℝ) * energy4 x0 x1 x2 x3 -
      cross4 (51 / 100) (9 / 25) (13 / 50) x0 x1 x2 x3 =
        comparisonSOS x0 x1 x2 x3 := by
  unfold energy4 cross4 comparisonSOS
  ring

theorem comparison_sos_nonnegative_v2 (x0 x1 x2 x3 : ℝ) :
    0 ≤ comparisonSOS x0 x1 x2 x3 := by
  unfold comparisonSOS
  positivity

theorem cross_le_158_over_125_v2 (x0 x1 x2 x3 : ℝ) :
    cross4 (51 / 100) (9 / 25) (13 / 50) x0 x1 x2 x3 ≤
      (158 / 125 : ℝ) * energy4 x0 x1 x2 x3 := by
  have hi := comparison_sos_identity_v2 x0 x1 x2 x3
  have hp := comparison_sos_nonnegative_v2 x0 x1 x2 x3
  linarith

/-- Smaller nonnegative farthest bounds can use the same certificate when
x_i are coefficient norms. The farthest pair is never silently discarded. -/
theorem cross_le_of_farthest_bound_v2 (r x0 x1 x2 x3 : ℝ)
    (hr : r ≤ (13 / 50 : ℝ)) (hx0 : 0 ≤ x0) (hx3 : 0 ≤ x3) :
    cross4 (51 / 100) (9 / 25) r x0 x1 x2 x3 ≤
      (158 / 125 : ℝ) * energy4 x0 x1 x2 x3 := by
  have hrm := mul_le_mul_of_nonneg_right hr (mul_nonneg hx0 hx3)
  have h := cross_le_158_over_125_v2 x0 x1 x2 x3
  unfold cross4 at *
  nlinarith

theorem diagonal_32_over_25_margin_v2 (x0 x1 x2 x3 : ℝ) :
    (2 / 125 : ℝ) * energy4 x0 x1 x2 x3 ≤
      (32 / 25 : ℝ) * energy4 x0 x1 x2 x3 -
        cross4 (51 / 100) (9 / 25) (13 / 50) x0 x1 x2 x3 := by
  have h := cross_le_158_over_125_v2 x0 x1 x2 x3
  linarith

end AEGIS.RHFourBlockComparisonV2

#print axioms AEGIS.RHFourBlockComparisonV2.sector_decomposition_v2
#print axioms AEGIS.RHFourBlockComparisonV2.nine_eighths_counterexample_v2
#print axioms AEGIS.RHFourBlockComparisonV2.nine_eighths_not_universal_v2
#print axioms AEGIS.RHFourBlockComparisonV2.comparison_sos_identity_v2
#print axioms AEGIS.RHFourBlockComparisonV2.cross_le_158_over_125_v2
#print axioms AEGIS.RHFourBlockComparisonV2.cross_le_of_farthest_bound_v2
#print axioms AEGIS.RHFourBlockComparisonV2.diagonal_32_over_25_margin_v2
