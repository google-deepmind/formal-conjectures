import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Finite three-block rational budget

Source context: Aegis-Omega/AEGIS-OMEGA PR #494,
cf660498847634a5a45fc6c19644132be3ec8417.
Input receipt SHA-256:
649ec8b74944271593b68bb9a9584c691e19e72c524401eb3d2d1bdc91638cc2.

Scope: exact rational enclosures, a three-variable sum-of-squares identity,
and conditional finite quadratic-budget implications. The input receipt is
provenance, not a Lean premise or an oracle. Its analytic interpretations
are NOT established here.

There is no import of the repository Weil definitions, no identification
with an analytic Gram matrix, and no operator-norm theorem in this file.
Global Weil sign remains OPEN; RH remains NOT_PROVEN; authority_effect=NONE.
-/

noncomputable section
namespace AEGIS.WeilThreeBlockRationalV1

/-- Arithmetic on the proposed rational endpoints, not analytic enclosures. -/
theorem rational_enclosures :
    (103 : ℚ) / 100 < 32449 / 31500 ∧
    (1 : ℚ) / 2 + 75 / 9086 = 2309 / 4543 ∧
    (2309 : ℚ) / 4543 < 51 / 100 ∧
    (7 : ℚ) / 20 + 15 / 13216 = 23203 / 66080 ∧
    (23203 : ℚ) / 66080 < 9 / 25 := by
  norm_num

/-- M has off-diagonal entries (51/100, 9/25, 51/100), w=(1,11/10,1).
These are the three coordinates of (93/100)w-Mw. -/
theorem rational_schur_rows :
    (93 : ℚ) / 100 - ((51 : ℚ) / 100 * (11 / 10) + 9 / 25) = 9 / 1000 ∧
    (93 : ℚ) / 100 * (11 / 10) - (51 / 100 + 51 / 100) = 3 / 1000 ∧
    (93 : ℚ) / 100 - (9 / 25 + (51 : ℚ) / 100 * (11 / 10)) = 9 / 1000 := by
  norm_num

/-- Exact scalar budget subtraction and normalization. -/
theorem rational_budget :
    (103 : ℚ) / 100 - 93 / 100 = 1 / 10 ∧
    ((93 : ℚ) / 100) / (103 / 100) = 93 / 103 ∧
    (0 : ℚ) < 93 / 103 ∧
    (93 : ℚ) / 103 < 1 := by
  norm_num

def energy (x y z : ℝ) : ℝ := x ^ 2 + y ^ 2 + z ^ 2

def offdiagMajorant (x y z : ℝ) : ℝ :=
  2 * ((51 / 100 : ℝ) * x * y + (9 / 25 : ℝ) * x * z +
    (51 / 100 : ℝ) * y * z)

/-- This proves the finite Schur estimate directly, without spectral theory. -/
theorem schur_sos_identity (x y z : ℝ) :
    (93 / 100 : ℝ) * energy x y z - offdiagMajorant x y z =
      (51 / 11000 : ℝ) * (11 * x - 10 * y) ^ 2 +
      (9 / 25 : ℝ) * (x - z) ^ 2 +
      (51 / 11000 : ℝ) * (10 * y - 11 * z) ^ 2 +
      (9 / 1000 : ℝ) * x ^ 2 +
      (3 / 1100 : ℝ) * y ^ 2 +
      (9 / 1000 : ℝ) * z ^ 2 := by
  dsimp [energy, offdiagMajorant]
  ring

theorem energy_nonneg (x y z : ℝ) : 0 ≤ energy x y z := by
  unfold energy
  positivity

theorem offdiag_majorant_le (x y z : ℝ) :
    offdiagMajorant x y z ≤ (93 / 100 : ℝ) * energy x y z := by
  rw [← sub_nonneg, schur_sos_identity]
  positivity

/-- A finite diagonal lower bound, with all three entry bounds explicit. -/
theorem diagonal_budget_lower (d0 d1 d2 x y z : ℝ)
    (h0 : (103 / 100 : ℝ) ≤ d0)
    (h1 : (103 / 100 : ℝ) ≤ d1)
    (h2 : (103 / 100 : ℝ) ≤ d2) :
    (103 / 100 : ℝ) * energy x y z ≤ d0 * x ^ 2 + d1 * y ^ 2 + d2 * z ^ 2 := by
  have hx := mul_le_mul_of_nonneg_right h0 (sq_nonneg x)
  have hy := mul_le_mul_of_nonneg_right h1 (sq_nonneg y)
  have hz := mul_le_mul_of_nonneg_right h2 (sq_nonneg z)
  unfold energy
  nlinarith

/-- Conditional finite negativity margin; d and r are arbitrary real scalars.
Applying this to an analytic form requires separately proved hd and hr. -/
theorem finite_budget_margin (x y z d r : ℝ)
    (hd : (103 / 100 : ℝ) * energy x y z ≤ d)
    (hr : r ≤ offdiagMajorant x y z) :
    -d + r ≤ -(1 / 10 : ℝ) * energy x y z := by
  have hmajor := offdiag_majorant_le x y z
  linarith

/-- A relative quadratic-budget inequality, NOT an operator-norm statement. -/
theorem finite_abs_relative_budget (x y z d r : ℝ)
    (hd : (103 / 100 : ℝ) * energy x y z ≤ d)
    (hr : |r| ≤ offdiagMajorant x y z) :
    |r| ≤ (93 / 103 : ℝ) * d := by
  calc
    |r| ≤ offdiagMajorant x y z := hr
    _ ≤ (93 / 100 : ℝ) * energy x y z := offdiag_majorant_le x y z
    _ = (93 / 103 : ℝ) * ((103 / 100 : ℝ) * energy x y z) := by ring
    _ ≤ (93 / 103 : ℝ) * d := mul_le_mul_of_nonneg_left hd (by norm_num)

/-- Strictness requires positive energy; the zero vector is not excluded silently. -/
theorem strict_negative_of_energy_pos (x y z d r : ℝ)
    (hd : (103 / 100 : ℝ) * energy x y z ≤ d)
    (hr : r ≤ offdiagMajorant x y z)
    (hE : 0 < energy x y z) :
    -d + r < 0 := by
  have hmargin := finite_budget_margin x y z d r hd hr
  have hneg : -(1 / 10 : ℝ) * energy x y z < 0 :=
    mul_neg_of_neg_of_pos (by norm_num) hE
  exact lt_of_le_of_lt hmargin hneg

/-- The tighter fixed-vector value in the receipt is distinct from a uniform bound. -/
theorem all_ones_value :
    -(103 / 100 : ℝ) * energy 1 1 1 + offdiagMajorant 1 1 1 = -(33 / 100 : ℝ) := by
  norm_num [energy, offdiagMajorant]

/-- Regression witness: 9/10 is too small for this rational majorant. -/
theorem rate_nine_tenths_is_too_small :
    (9 / 10 : ℝ) * energy 10 11 10 < offdiagMajorant 10 11 10 := by
  norm_num [energy, offdiagMajorant]

end AEGIS.WeilThreeBlockRationalV1

#print axioms AEGIS.WeilThreeBlockRationalV1.rational_enclosures
#print axioms AEGIS.WeilThreeBlockRationalV1.rational_schur_rows
#print axioms AEGIS.WeilThreeBlockRationalV1.rational_budget
#print axioms AEGIS.WeilThreeBlockRationalV1.schur_sos_identity
#print axioms AEGIS.WeilThreeBlockRationalV1.energy_nonneg
#print axioms AEGIS.WeilThreeBlockRationalV1.offdiag_majorant_le
#print axioms AEGIS.WeilThreeBlockRationalV1.diagonal_budget_lower
#print axioms AEGIS.WeilThreeBlockRationalV1.finite_budget_margin
#print axioms AEGIS.WeilThreeBlockRationalV1.finite_abs_relative_budget
#print axioms AEGIS.WeilThreeBlockRationalV1.strict_negative_of_energy_pos
#print axioms AEGIS.WeilThreeBlockRationalV1.all_ones_value
#print axioms AEGIS.WeilThreeBlockRationalV1.rate_nine_tenths_is_too_small
