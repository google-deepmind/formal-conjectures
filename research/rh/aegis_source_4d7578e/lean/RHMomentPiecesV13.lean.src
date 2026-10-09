import RHDyadicDiagonalV13
import WeilAutocorrelationRealityV1
import Mathlib.Tactic

/-!
AEGIS Ω — moment pieces for the narrow-packet diagonal, V13.

Elementary real-analysis pieces and one arithmetic vanishing statement:

* `lamR r = 1 / (sinh r · (1 + e^{-r}))`, positive for `r > 0`;
* the kernel `1/sinh u − lamR r · (1 + e^{-u})` is `≥ 0` on `0 < u ≤ r`
  and `≤ 0` on `u ≥ r > 0` (monotonicity of `sinh u · (1 + e^{-u})`);
* `(e^{u/2} − 1)/sinh u ≤ e^{r/2}/2` on `0 < u ≤ r`;
* `∫_{(a,b]} cosh(u/2) = 2 (sinh(b/2) − sinh(a/2))`;
* `∫_{(a,b]} 1/sinh u = cothTail a − cothTail b` for `0 < a ≤ b`;
* `4 · lamR r · (sinh r − 2 sinh(r/2)) ≤ 4 (cosh(r/2) − 1)` for `r > 0`;
* if `g` has log-half-width `r` with `2r < log 2`, the repository prime sum
  of its autocorrelation is exactly `0`.

Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHMomentPiecesV13
open AEGIS.RHDyadicDiagonalV13

def lamR (r : ℝ) : ℝ := 1 / (Real.sinh r * (1 + Real.exp (-r)))

theorem lamR_pos (r : ℝ) (hr : 0 < r) : 0 < lamR r := by
  unfold lamR
  have := Real.sinh_pos_iff.mpr hr
  positivity

/-- `s(u) = sinh u · (1 + e^{-u})` is monotone. -/
theorem s_mono {u r : ℝ} (hur : u ≤ r) :
    Real.sinh u * (1 + Real.exp (-u)) ≤ Real.sinh r * (1 + Real.exp (-r)) := by
  have key : ∀ x : ℝ, Real.sinh x * (1 + Real.exp (-x)) =
      (Real.exp x + 1 - Real.exp (-x) - Real.exp (-x) ^ 2) / 2 := by
    intro x
    have h1 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    rw [Real.sinh_eq]
    linear_combination (1 / 2 : ℝ) * h1
  rw [key, key]
  have h1 : Real.exp u ≤ Real.exp r := Real.exp_le_exp.mpr hur
  have h2 : Real.exp (-r) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
  have h3 : 0 < Real.exp (-r) := Real.exp_pos _
  nlinarith

theorem kernel_nonneg (r u : ℝ) (hu0 : 0 < u) (hur : u ≤ r) :
    0 ≤ 1 / Real.sinh u - lamR r * (1 + Real.exp (-u)) := by
  have hsu : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  have he : 0 < 1 + Real.exp (-u) := by positivity
  have hSu : 0 < Real.sinh u * (1 + Real.exp (-u)) := mul_pos hsu he
  have hm := s_mono hur
  have heq : 1 / Real.sinh u = (1 + Real.exp (-u)) / (Real.sinh u * (1 + Real.exp (-u))) := by
    field_simp
  have heq2 : lamR r * (1 + Real.exp (-u)) =
      (1 + Real.exp (-u)) / (Real.sinh r * (1 + Real.exp (-r))) := by
    unfold lamR; ring
  rw [heq, heq2, sub_nonneg]
  exact div_le_div_of_nonneg_left he.le hSu hm

theorem kernel_nonpos (r u : ℝ) (hr0 : 0 < r) (hru : r ≤ u) :
    1 / Real.sinh u - lamR r * (1 + Real.exp (-u)) ≤ 0 := by
  have hu0 : 0 < u := lt_of_lt_of_le hr0 hru
  have hsu : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  have hsr : 0 < Real.sinh r := Real.sinh_pos_iff.mpr hr0
  have he : 0 < 1 + Real.exp (-u) := by positivity
  have hSr : 0 < Real.sinh r * (1 + Real.exp (-r)) := mul_pos hsr (by positivity)
  have hm := s_mono hru
  have heq : 1 / Real.sinh u = (1 + Real.exp (-u)) / (Real.sinh u * (1 + Real.exp (-u))) := by
    field_simp
  have heq2 : lamR r * (1 + Real.exp (-u)) =
      (1 + Real.exp (-u)) / (Real.sinh r * (1 + Real.exp (-r))) := by
    unfold lamR; ring
  rw [heq, heq2, sub_nonpos]
  exact div_le_div_of_nonneg_left he.le hSr hm

theorem inner_pointwise (r u : ℝ) (hu0 : 0 < u) (hur : u ≤ r) :
    (Real.exp (u / 2) - 1) / Real.sinh u ≤ Real.exp (r / 2) / 2 := by
  have hsu : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  have hself : u ≤ Real.sinh u := Real.self_le_sinh_iff.mpr hu0.le
  -- `e^x − 1 ≤ x e^x`
  have hx : Real.exp (u / 2) - 1 ≤ (u / 2) * Real.exp (u / 2) := by
    have h := Real.add_one_le_exp (-(u / 2))
    have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos (u / 2)).le
    have hprod : Real.exp (u / 2) * Real.exp (-(u / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [hmul, hprod]
  have hmono : Real.exp (u / 2) ≤ Real.exp (r / 2) := Real.exp_le_exp.mpr (by linarith)
  rw [div_le_iff₀ hsu]
  have hpos := Real.exp_pos (u / 2)
  nlinarith [mul_le_mul_of_nonneg_left hmono (by linarith : (0 : ℝ) ≤ u / 2),
    mul_le_mul_of_nonneg_right hself (Real.exp_pos (r / 2)).le]

theorem integral_cosh_half (a b : ℝ) (hab : a ≤ b) :
    ∫ u in Ioc a b, Real.cosh (u / 2) = 2 * (Real.sinh (b / 2) - Real.sinh (a / 2)) := by
  rw [← intervalIntegral.integral_of_le hab]
  have hderiv : ∀ u ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ => 2 * Real.sinh (x / 2)) (Real.cosh (u / 2)) u := by
    intro u _
    have h := ((Real.hasDerivAt_sinh (u / 2)).comp u ((hasDerivAt_id u).div_const 2)).const_mul 2
    have h2 : 2 * (Real.cosh (u / 2) * (1 / 2)) = Real.cosh (u / 2) := by ring
    rw [h2] at h
    exact h
  have hcont : Continuous (fun u : ℝ => Real.cosh (u / 2)) :=
    Real.continuous_cosh.comp (continuous_id.div_const 2)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable a b)]
  ring

theorem integral_inv_sinh_Ioc (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ u in Ioc a b, 1 / Real.sinh u = cothTail a - cothTail b := by
  rw [← intervalIntegral.integral_of_le hab, cothTail_sub a b ha hab]

theorem lam_term_le (r : ℝ) (hr : 0 < r) :
    4 * lamR r * (Real.sinh r - 2 * Real.sinh (r / 2)) ≤ 4 * (Real.cosh (r / 2) - 1) := by
  have hsh : 0 < Real.sinh (r / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have hch : 1 ≤ Real.cosh (r / 2) := Real.one_le_cosh _
  have he : 0 < Real.exp (-r) := Real.exp_pos _
  have hsr : Real.sinh r = 2 * Real.sinh (r / 2) * Real.cosh (r / 2) := by
    rw [← Real.sinh_two_mul]; ring_nf
  have hD : 1 ≤ Real.cosh (r / 2) * (1 + Real.exp (-r)) := by nlinarith
  have hlhs : 4 * lamR r * (Real.sinh r - 2 * Real.sinh (r / 2)) =
      4 * ((Real.cosh (r / 2) - 1) / (Real.cosh (r / 2) * (1 + Real.exp (-r)))) := by
    unfold lamR
    rw [hsr]
    have : 0 < Real.cosh (r / 2) := by linarith
    field_simp
  rw [hlhs]
  have := div_le_self (by linarith : (0 : ℝ) ≤ Real.cosh (r / 2) - 1) hD
  linarith

theorem prime_sum_zero_of_halfWidth (g : WeilCompactSmoothGV1) (r a : ℝ)
    (hw : HalfWidthAt g r a) (hr : 2 * r < Real.log 2) :
    WeilPrimeSumV1 (WeilAutocorrelationV1 g) = 0 := by
  have hterm : ∀ n : ℕ, WeilPrimeTermV1 (WeilAutocorrelationV1 g) n = 0 := by
    intro n
    rcases n with _ | n
    · simp [WeilPrimeTermV1]
    · have hm2R : (2 : ℝ) ≤ ((n + 1 + 1 : ℕ) : ℝ) := by push_cast; linarith [n.cast_nonneg (α := ℝ)]
      have hmpos : (0 : ℝ) < ((n + 1 + 1 : ℕ) : ℝ) := by linarith
      have hlog : Real.log 2 ≤ Real.log ((n + 1 + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by norm_num) hm2R
      have hA : WeilAutocorrelationV1 g ((n + 1 + 1 : ℕ) : ℝ) = 0 := by
        have h := autocorrelation_zero_of_halfWidth g r a (Real.log ((n + 1 + 1 : ℕ) : ℝ)) hw
          (by linarith)
        rwa [Real.exp_log hmpos] at h
      have hAi : WeilAutocorrelationV1 g (((n + 1 + 1 : ℕ) : ℝ))⁻¹ = 0 := by
        rw [weil_autocorrelation_reciprocal_v1 g hmpos, hA]
        simp
      change ((ArithmeticFunction.vonMangoldt (n + 1 + 1) : ℝ) : ℂ) *
        (WeilAutocorrelationV1 g ((n + 1 + 1 : ℕ) : ℝ) +
          (1 / ((n + 1 + 1 : ℕ) : ℂ)) * WeilAutocorrelationV1 g (((n + 1 + 1 : ℕ) : ℝ))⁻¹) = 0
      rw [hA, hAi]
      simp
  unfold WeilPrimeSumV1
  have hzero : WeilPrimeTermV1 (WeilAutocorrelationV1 g) = fun _ : ℕ => (0 : ℂ) :=
    funext hterm
  rw [hzero]
  exact tsum_zero

end AEGIS.RHMomentPiecesV13

#print axioms AEGIS.RHMomentPiecesV13.lamR_pos
#print axioms AEGIS.RHMomentPiecesV13.kernel_nonneg
#print axioms AEGIS.RHMomentPiecesV13.kernel_nonpos
#print axioms AEGIS.RHMomentPiecesV13.inner_pointwise
#print axioms AEGIS.RHMomentPiecesV13.integral_cosh_half
#print axioms AEGIS.RHMomentPiecesV13.integral_inv_sinh_Ioc
#print axioms AEGIS.RHMomentPiecesV13.lam_term_le
#print axioms AEGIS.RHMomentPiecesV13.prime_sum_zero_of_halfWidth
