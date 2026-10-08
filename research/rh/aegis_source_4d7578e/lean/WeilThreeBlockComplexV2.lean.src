import WeilThreeBlockRationalV1
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
Quotient-free complex coefficient lift of the checked rational certificate.
All diagonal and pairwise analytic estimates remain explicit hypotheses.
No nonzero block-norm assumption. No operator-norm or global Weil conclusion.
-/
open Complex
open scoped ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace AEGIS.WeilThreeBlockComplexV2
open AEGIS.WeilThreeBlockRationalV1

def weightedEnergy (z0 z1 z2 : ℂ) (r0 r1 r2 : ℝ) : ℝ :=
  energy (‖z0‖ * r0) (‖z1‖ * r1) (‖z2‖ * r2)

def diagonal (z0 z1 z2 : ℂ) (d0 d1 d2 : ℝ) : ℝ :=
  ‖z0‖ ^ 2 * d0 + ‖z1‖ ^ 2 * d1 + ‖z2‖ ^ 2 * d2

def cross (z0 z1 z2 b01 b02 b12 : ℂ) : ℝ :=
  2 * (z0 * star z1 * b01 + z0 * star z2 * b02 + z1 * star z2 * b12).re

theorem energy_expansion (z0 z1 z2 : ℂ) (r0 r1 r2 : ℝ) :
    weightedEnergy z0 z1 z2 r0 r1 r2 =
      ‖z0‖ ^ 2 * r0 ^ 2 + ‖z1‖ ^ 2 * r1 ^ 2 + ‖z2‖ ^ 2 * r2 ^ 2 := by
  unfold weightedEnergy energy
  ring

theorem weighted_diagonal (z0 z1 z2 : ℂ) (r0 r1 r2 d0 d1 d2 : ℝ)
    (h0 : (103 / 100 : ℝ) * r0 ^ 2 ≤ d0)
    (h1 : (103 / 100 : ℝ) * r1 ^ 2 ≤ d1)
    (h2 : (103 / 100 : ℝ) * r2 ^ 2 ≤ d2) :
    (103 / 100 : ℝ) * weightedEnergy z0 z1 z2 r0 r1 r2 ≤
      diagonal z0 z1 z2 d0 d1 d2 := by
  have h0' := mul_le_mul_of_nonneg_left h0 (sq_nonneg ‖z0‖)
  have h1' := mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖z1‖)
  have h2' := mul_le_mul_of_nonneg_left h2 (sq_nonneg ‖z2‖)
  rw [energy_expansion]
  unfold diagonal
  nlinarith

theorem weighted_pair (z w b : ℂ) (c r s : ℝ) (hb : ‖b‖ ≤ c * r * s) :
    (z * star w * b).re ≤ c * (‖z‖ * r) * (‖w‖ * s) := by
  calc
    (z * star w * b).re ≤ ‖z * star w * b‖ := Complex.re_le_norm _
    _ = (‖z‖ * ‖w‖) * ‖b‖ := by simp only [norm_mul, norm_star]
    _ ≤ (‖z‖ * ‖w‖) * (c * r * s) :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = c * (‖z‖ * r) * (‖w‖ * s) := by ring

theorem weighted_cross (z0 z1 z2 b01 b02 b12 : ℂ) (r0 r1 r2 : ℝ)
    (h01 : ‖b01‖ ≤ (51 / 100 : ℝ) * r0 * r1)
    (h02 : ‖b02‖ ≤ (9 / 25 : ℝ) * r0 * r2)
    (h12 : ‖b12‖ ≤ (51 / 100 : ℝ) * r1 * r2) :
    cross z0 z1 z2 b01 b02 b12 ≤
      offdiagMajorant (‖z0‖ * r0) (‖z1‖ * r1) (‖z2‖ * r2) := by
  have h01' := weighted_pair z0 z1 b01 (51/100) r0 r1 h01
  have h02' := weighted_pair z0 z2 b02 (9/25) r0 r2 h02
  have h12' := weighted_pair z1 z2 b12 (51/100) r1 r2 h12
  unfold cross offdiagMajorant
  simp only [Complex.add_re]
  linarith

theorem quotient_free_margin (z0 z1 z2 b01 b02 b12 : ℂ) (r0 r1 r2 d0 d1 d2 : ℝ)
    (h0 : (103 / 100 : ℝ) * r0 ^ 2 ≤ d0)
    (h1 : (103 / 100 : ℝ) * r1 ^ 2 ≤ d1)
    (h2 : (103 / 100 : ℝ) * r2 ^ 2 ≤ d2)
    (h01 : ‖b01‖ ≤ (51 / 100 : ℝ) * r0 * r1)
    (h02 : ‖b02‖ ≤ (9 / 25 : ℝ) * r0 * r2)
    (h12 : ‖b12‖ ≤ (51 / 100 : ℝ) * r1 * r2) :
    -diagonal z0 z1 z2 d0 d1 d2 + cross z0 z1 z2 b01 b02 b12 ≤
      -(1 / 10 : ℝ) * weightedEnergy z0 z1 z2 r0 r1 r2 := by
  exact finite_budget_margin (‖z0‖ * r0) (‖z1‖ * r1) (‖z2‖ * r2)
    (diagonal z0 z1 z2 d0 d1 d2) (cross z0 z1 z2 b01 b02 b12)
    (weighted_diagonal z0 z1 z2 r0 r1 r2 d0 d1 d2 h0 h1 h2)
    (weighted_cross z0 z1 z2 b01 b02 b12 r0 r1 r2 h01 h02 h12)

/-- Nonnegativity applies to arbitrary complex coefficients, including all zero. -/
theorem energy_nonnegative (z0 z1 z2 : ℂ) (r0 r1 r2 : ℝ) :
    0 ≤ weightedEnergy z0 z1 z2 r0 r1 r2 := energy_nonneg _ _ _

/-- A concrete negative control for dropping conjugation from a pair. -/
theorem conjugation_matters :
    ((Complex.I) * star (Complex.I) * (1 : ℂ)).re ≠
      ((Complex.I) * (Complex.I) * (1 : ℂ)).re := by norm_num

end AEGIS.WeilThreeBlockComplexV2
