import WeilWidthArchIntegralV27
import Mathlib.Tactic

/-!
AEGIS Ω — translated three-block mixed-correlation transport V2.8.

This lane attacks only the remaining cross-term frontier after V2.7 closed the
retained width-1/32 diagonal estimate.

For arbitrary compact-smooth packets a,b define the additive-coordinate mixed
correlation
  X_{a,b}(u) = ∫ logLift(a)(v+u) * conj(logLift(b)(v)) dv.
It satisfies
  X_{a,b}(u) = exp(u/2) * mixed(a,b)(exp u).

For two translates of one retained packet g this collapses to the already
verified V2.5 autocorrelation:
  exp(u/2) * mixed(T_d1 g,T_d2 g)(exp u)
    = C_g(u + d2 - d1).

This module also proves two-sided width vanishing.  It does not yet assert the
51/100 or 9/25 cross B bounds, global Weil positivity, or RH.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilThreeBlockCrossPrimeV28

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.WeilDiagonalKernelReductionV21

def logCrossV28
    (a b : WeilCompactSmoothGV1) (u : ℝ) : ℂ :=
  ∫ v : ℝ, logLift a.1 (v + u) * conj (logLift b.1 v)

/-- Exact multiplicative-to-additive identity for the actual repository mixed
correlation. -/
theorem logCross_eq_mixed_v28
    (a b : WeilCompactSmoothGV1) (u : ℝ) :
    logCrossV28 a b u =
      (Real.exp (u / 2) : ℂ) * mixed a b (Real.exp u) := by
  unfold logCrossV28 mixed
  rw [integral_exp_substitution_complex]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  unfold logLift
  rw [Complex.star_def, map_mul]
  simp only [Complex.conj_ofReal, Complex.real_smul]
  have harg :
      Real.exp u * Real.exp v = Real.exp (v + u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [harg]
  have hscalar :
      (Real.exp (u / 2) : ℂ) * (Real.exp v : ℂ) =
        (Real.exp ((v + u) / 2) : ℂ) *
          (Real.exp (v / 2) : ℂ) := by
    norm_cast
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    (Real.exp ((v + u) / 2) : ℂ) * a.1 (Real.exp (v + u)) *
        ((Real.exp (v / 2) : ℂ) * conj (b.1 (Real.exp v)))
        =
      ((Real.exp ((v + u) / 2) : ℂ) *
          (Real.exp (v / 2) : ℂ)) *
        (a.1 (Real.exp (v + u)) * conj (b.1 (Real.exp v))) := by
          ring
    _ =
      ((Real.exp (u / 2) : ℂ) * (Real.exp v : ℂ)) *
        (a.1 (Real.exp (v + u)) * conj (b.1 (Real.exp v))) := by
          rw [← hscalar]
    _ =
      (Real.exp (u / 2) : ℂ) *
        ((Real.exp v : ℂ) *
          (a.1 (Real.exp (v + u)) * conj (b.1 (Real.exp v)))) := by
          ring

/-- Translating both packets converts the mixed log correlation into the base
packet's V2.5 autocorrelation, depending only on the relative shift. -/
theorem logCross_translate_eq_logCorrelation_v28
    (g : WeilCompactSmoothGV1) (d1 d2 u : ℝ) :
    logCrossV28 (translatePacket g d1) (translatePacket g d2) u =
      logCorrelationV25 g (u + d2 - d1) := by
  unfold logCrossV28 logCorrelationV25
  simp_rw [logLift_translate]
  let F : ℝ → ℂ := fun w =>
    logLift g.1 (w + (u + d2 - d1)) * conj (logLift g.1 w)
  calc
    (∫ v : ℝ,
      logLift g.1 (v + u - d1) * conj (logLift g.1 (v - d2)))
        =
      ∫ v : ℝ, F (v + (-d2)) := by
        apply integral_congr_ae
        filter_upwards [] with v
        dsimp [F]
        congr 2
        congr 1
        ring
    _ = ∫ w : ℝ, F w := integral_add_right_eq_self F (-d2)
    _ = ∫ w : ℝ,
      logLift g.1 (w + (u + d2 - d1)) * conj (logLift g.1 w) := by
        rfl

/-- Load-bearing transport identity for the retained translated packet family. -/
theorem exp_half_mul_mixed_translate_v28
    (g : WeilCompactSmoothGV1) (d1 d2 u : ℝ) :
    (Real.exp (u / 2) : ℂ) *
        mixed (translatePacket g d1) (translatePacket g d2) (Real.exp u) =
      logCorrelationV25 g (u + d2 - d1) := by
  rw [← logCross_eq_mixed_v28]
  exact logCross_translate_eq_logCorrelation_v28 g d1 d2 u

/-- Width-1/32 support kills the V2.5 log correlation on both sides of the
difference-support interval. -/
theorem logCorrelation_zero_of_width_abs_v28
    (g : WeilCompactSmoothGV1) (a u : ℝ)
    (hw : WidthOneThirtyTwoAt g a)
    (hu : (1 / 32 : ℝ) < |u|) :
    logCorrelationV25 g u = 0 := by
  unfold logCorrelationV25
  apply integral_eq_zero_of_ae
  filter_upwards [] with v
  by_cases h0 : logLift g.1 v = 0
  · simp [h0]
  · by_cases h1 : logLift g.1 (v + u) = 0
    · simp [h1]
    · have hm0 : v ∈ tsupport (logLift g.1) :=
        subset_tsupport _ h0
      have hm1 : v + u ∈ tsupport (logLift g.1) :=
        subset_tsupport _ h1
      have hv := hw hm0
      have hvu := hw hm1
      have habs : |u| ≤ (1 / 32 : ℝ) := by
        rw [abs_le]
        constructor <;> linarith [hv.1, hv.2, hvu.1, hvu.2]
      exact False.elim ((not_le_of_gt hu) habs)

/-- Hence the actual translated mixed correlation vanishes whenever its
relative log displacement lies outside the width-1/32 window. -/
theorem mixed_translate_zero_of_width_v28
    (g : WeilCompactSmoothGV1) (a d1 d2 u : ℝ)
    (hw : WidthOneThirtyTwoAt g a)
    (hu : (1 / 32 : ℝ) < |u + d2 - d1|) :
    mixed (translatePacket g d1) (translatePacket g d2) (Real.exp u) = 0 := by
  have h :=
    exp_half_mul_mixed_translate_v28 g d1 d2 u
  rw [logCorrelation_zero_of_width_abs_v28 g a (u + d2 - d1) hw hu] at h
  have he : (Real.exp (u / 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  exact (mul_eq_zero.mp h).resolve_left he

/-- The centered log correlation is exactly the packet energy, as a complex
number. -/
theorem logCorrelation_zero_eq_energy_v28
    (g : WeilCompactSmoothGV1) :
    logCorrelationV25 g 0 = (energy g.1 : ℂ) := by
  rw [logCorrelation_eq_autocorrelation_v25]
  simp only [zero_div, Real.exp_zero, Complex.ofReal_one, one_mul]
  apply Complex.ext
  · simpa using
      (AEGIS.WeilDiagonalKernelReductionV21.autocorrelation_one_re_eq_energy g)
  · simpa using (weil_autocorrelation_one_real_v1 g)

/-- Exact center value for any pair of translates. -/
theorem mixed_translate_center_v28
    (g : WeilCompactSmoothGV1) (d1 d2 : ℝ) :
    (Real.exp ((d1 - d2) / 2) : ℂ) *
        mixed (translatePacket g d1) (translatePacket g d2)
          (Real.exp (d1 - d2)) =
      (energy g.1 : ℂ) := by
  have h :=
    exp_half_mul_mixed_translate_v28 g d1 d2 (d1 - d2)
  have hz : d1 - d2 + d2 - d1 = 0 := by ring
  rw [hz, logCorrelation_zero_eq_energy_v28] at h
  exact h

end AEGIS.WeilThreeBlockCrossPrimeV28

#print axioms AEGIS.WeilThreeBlockCrossPrimeV28.logCross_eq_mixed_v28
#print axioms AEGIS.WeilThreeBlockCrossPrimeV28.logCross_translate_eq_logCorrelation_v28
#print axioms AEGIS.WeilThreeBlockCrossPrimeV28.exp_half_mul_mixed_translate_v28
#print axioms AEGIS.WeilThreeBlockCrossPrimeV28.logCorrelation_zero_of_width_abs_v28
#print axioms AEGIS.WeilThreeBlockCrossPrimeV28.mixed_translate_zero_of_width_v28
#print axioms AEGIS.WeilThreeBlockCrossPrimeV28.mixed_translate_center_v28
