import WeilThreeBlockTranslatedPacketsV22
import WeilAutocorrelationRealityV1
import WeilPrimeSummabilityV1
import Mathlib.Tactic

/-!
AEGIS Ω — width-1/32 diagonal prime vanishing V2.3

Parent exact head:
  7e3c85664c65faf1e02f6887c22b4350386a1af8

This module closes only the non-Archimedean diagonal term for the retained
width-1/32 packet family.  It proves directly from logarithmic support that the
repository autocorrelation vanishes at every x >= 2, then uses the already
verified reciprocal identity for x^{-1}.  Hence every repository prime term is
zero and the full prime `tsum` is zero.

No Archimedean inequality, cross-term majorant, global Weil sign, or RH is
proved here.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilWidthPrimeVanishingV23

open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockAnalyticConstantsV21

/-- Width-1/32 log support forces the multiplicative autocorrelation to vanish
at every scale x >= 2. -/
theorem autocorrelation_zero_of_ge_two
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a)
    {x : ℝ} (hx : 2 ≤ x) :
    WeilAutocorrelationV1 g x = 0 := by
  unfold WeilAutocorrelationV1
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : 0 < y
  · by_cases hgy : g.1 y = 0
    · simp [hgy]
    · by_cases hgxy : g.1 (x * y) = 0
      · simp [hgxy]
      · have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
        have hxypos : 0 < x * y := mul_pos hxpos hy
        have hylog :=
          log_mem_of_ne_zero g hw hy hgy
        have hxylog :=
          log_mem_of_ne_zero g hw hxypos hgxy
        have hlogmul :
            Real.log (x * y) = Real.log x + Real.log y := by
          rw [Real.log_mul hxpos.ne' hy.ne']
        rw [hlogmul] at hxylog
        have hlogx :
            (1 / 32 : ℝ) < Real.log x := by
          exact log_two_gt_one_thirty_two.trans_le
            (Real.log_le_log (by norm_num) hx)
        exfalso
        linarith [hylog.1, hylog.2, hxylog.1, hxylog.2, hlogx]
  · have hgy : g.1 y = 0 :=
      packet_eq_zero_of_nonpos g (le_of_not_gt hy)
    simp [hgy]

/-- The reciprocal autocorrelation sample also vanishes at every x >= 2. -/
theorem autocorrelation_inv_zero_of_ge_two
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a)
    {x : ℝ} (hx : 2 ≤ x) :
    WeilAutocorrelationV1 g x⁻¹ = 0 := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  rw [weil_autocorrelation_reciprocal_v1 g hxpos]
  rw [autocorrelation_zero_of_ge_two g a hw hx]
  simp

/-- Every positive-integer prime-power term on the diagonal is zero. -/
theorem diagonal_prime_term_zero
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a)
    (n : ℕ) :
    WeilPrimeTermV1 (WeilAutocorrelationV1 g) n = 0 := by
  by_cases hn : n = 0
  · subst n
    simp [WeilPrimeTermV1]
  · have hm : 2 ≤ n + 1 := by omega
    have hp :
        WeilAutocorrelationV1 g ((n + 1 : ℕ) : ℝ) = 0 :=
      autocorrelation_zero_of_ge_two g a hw (by exact_mod_cast hm)
    have hi :
        WeilAutocorrelationV1 g (((n + 1 : ℕ) : ℝ)⁻¹) = 0 :=
      autocorrelation_inv_zero_of_ge_two g a hw (by exact_mod_cast hm)
    unfold WeilPrimeTermV1
    change ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) *
      (WeilAutocorrelationV1 g ((n + 1 : ℕ) : ℝ) +
        (1 / ((n + 1 : ℕ) : ℂ)) *
          WeilAutocorrelationV1 g (((n + 1 : ℕ) : ℝ)⁻¹)) = 0
    rw [hp, hi]
    ring

/-- Width-1/32 diagonal prime vanishing in the ACTUAL repository explicit-formula term. -/
theorem diagonal_prime_sum_zero
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a) :
    WeilPrimeSumV1 (WeilAutocorrelationV1 g) = 0 := by
  unfold WeilPrimeSumV1
  simp [diagonal_prime_term_zero g a hw]

#print axioms autocorrelation_zero_of_ge_two
#print axioms autocorrelation_inv_zero_of_ge_two
#print axioms diagonal_prime_term_zero
#print axioms diagonal_prime_sum_zero

end AEGIS.WeilWidthPrimeVanishingV23
