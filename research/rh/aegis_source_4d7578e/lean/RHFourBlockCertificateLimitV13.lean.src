import RHFourBlockComparisonV2
import Mathlib.Tactic

/-!
AEGIS Ω — where the four-block certificate schema stops, V13.

`RHFourBlockComparisonV2` certifies the four-translate family from a diagonal
floor `32/25` and cross-term norm ceilings `51/100`, `9/25`, `13/50` for gaps
`log 2`, `2 log 2`, `3 log 2`.  This module records, kernel-checked, that the
SAME schema cannot certify five equally spaced translates: there is a real
symmetric matrix obeying every one of those bounds whose quadratic form is
negative on the all-ones vector.  Since `actual_four_block_bound_v2` uses only
norm ceilings on the cross terms (no phase information), the five-block
analogue of that lemma is false as a statement about bounds, whatever the
fourth-gap ceiling `r ≥ 0` is.

This says nothing about the true Weil form on five translates.  It says the
repository's method — norm ceilings plus an SOS certificate — has no room
left past four blocks with these constants.  AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFourBlockCertificateLimitV13

open AEGIS.RHFourBlockComparisonV2

/-- Five-translate energy. -/
def energy5 (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2

/-- Five-translate cross form with gap-indexed coefficients
`a` (gap 1), `b` (gap 2), `c` (gap 3), `r` (gap 4). -/
def cross5 (a b c r x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  2 * (a * (x0 * x1 + x1 * x2 + x2 * x3 + x3 * x4) +
       b * (x0 * x2 + x1 * x3 + x2 * x4) +
       c * (x0 * x3 + x1 * x4) +
       r * x0 * x4)

/-- The four-block margin `2/125` is what the SOS certificate leaves. -/
theorem four_block_margin_positive :
    (0 : ℝ) < 32 / 25 - 158 / 125 := by norm_num

/-- With the repository's constants the five-block worst case is already
negative on the all-ones vector, for every nonnegative fourth-gap ceiling. -/
theorem five_block_all_ones_negative (r : ℝ) (hr : 0 ≤ r) :
    (32 / 25 : ℝ) * energy5 1 1 1 1 1 -
      cross5 (51 / 100) (9 / 25) (13 / 50) r 1 1 1 1 1 < 0 := by
  unfold energy5 cross5
  nlinarith

/-- Exact value with the fourth-gap ceiling set to zero: `6.4 − 7.28 = −0.88`. -/
theorem five_block_all_ones_value :
    (32 / 25 : ℝ) * energy5 1 1 1 1 1 -
      cross5 (51 / 100) (9 / 25) (13 / 50) 0 1 1 1 1 1 = -(22 / 25 : ℝ) := by
  norm_num [energy5, cross5]

/-- Hence no inequality of the shape
`cross5 (51/100) (9/25) (13/50) r x ≤ (32/25) · energy5 x` holds for all `x`,
so the five-block analogue of `cross_le_158_over_125_v2`-plus-margin is false. -/
theorem five_block_certificate_impossible (r : ℝ) (hr : 0 ≤ r) :
    ¬ (∀ x0 x1 x2 x3 x4 : ℝ,
      cross5 (51 / 100) (9 / 25) (13 / 50) r x0 x1 x2 x3 x4 ≤
        (32 / 25 : ℝ) * energy5 x0 x1 x2 x3 x4) := by
  intro h
  have := h 1 1 1 1 1
  have hneg := five_block_all_ones_negative r hr
  linarith

/-- Even the four-block constants alone (dropping the farthest pair entirely)
exceed the diagonal on the interior of a five-chain: `2·(51/100 + 9/25) > 32/25`. -/
theorem interior_row_exceeds_diagonal :
    (32 / 25 : ℝ) < 2 * (51 / 100 + 9 / 25) := by norm_num

end AEGIS.RHFourBlockCertificateLimitV13

#print axioms AEGIS.RHFourBlockCertificateLimitV13.five_block_all_ones_negative
#print axioms AEGIS.RHFourBlockCertificateLimitV13.five_block_certificate_impossible
#print axioms AEGIS.RHFourBlockCertificateLimitV13.interior_row_exceeds_diagonal
