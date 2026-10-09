import WeilWidthDiagonalArchFrontierV24
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
AEGIS Ω — width-1/32 logarithmic autocorrelation core V2.5.

For h(t)=exp(t/2) g(exp t), define
  C_g(u)=∫ h(v+u) conj(h(v)) dv.

This module proves three facts needed by the remaining Archimedean diagonal
budget:
1. C_g(u)=exp(u/2) A_g(exp u), where A_g is the repository autocorrelation;
2. ||C_g(u)|| <= energy(g), by the elementary 2ab <= a^2+b^2 bound and
   translation invariance of Lebesgue measure;
3. C_g(u)=0 for u>1/32 when g has the retained width-1/32 logarithmic support.

No Archimedean integral inequality, off-diagonal estimate, global Weil sign,
or RH conclusion is asserted here.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilWidthArchCorrelationV25

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilThreeBlockTranslatedPacketsV22

def logCorrelationV25 (g : WeilCompactSmoothGV1) (u : ℝ) : ℂ :=
  ∫ v : ℝ, logLift g.1 (v + u) * conj (logLift g.1 v)

private theorem logLift_continuous_v25 (g : WeilCompactSmoothGV1) :
    Continuous (logLift g.1) := by
  unfold logLift
  have hscalar : Continuous (fun t : ℝ =>
      (Real.exp (t / 2) : ℂ)) := by
    fun_prop
  have hpacket : Continuous (fun t : ℝ =>
      g.1 (Real.exp t)) :=
    g.2.1.continuous.comp Real.continuous_exp
  exact hscalar.mul hpacket

private theorem logLift_hasCompactSupport_v25 (g : WeilCompactSmoothGV1) :
    HasCompactSupport (logLift g.1) := by
  let K : Set ℝ := Real.log '' tsupport g.1
  have hK : IsCompact K := by
    have hlog : ContinuousOn Real.log (tsupport g.1) := by
      intro x hx
      exact (Real.continuousAt_log (ne_of_gt (g.2.2.2 hx))).continuousWithinAt
    exact g.2.2.1.image_of_continuousOn hlog
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro t ht
  have hg : g.1 (Real.exp t) ≠ 0 := by
    intro hzero
    apply ht
    simp [logLift, hzero]
  have hm : Real.exp t ∈ tsupport g.1 := subset_tsupport _ hg
  refine ⟨Real.exp t, hm, ?_⟩
  simp

theorem logLift_sq_integrable_v25 (g : WeilCompactSmoothGV1) :
    Integrable (fun v : ℝ => ‖logLift g.1 v‖ ^ 2) := by
  have hc : Continuous (fun v : ℝ => ‖logLift g.1 v‖ ^ 2) := by
    exact (logLift_continuous_v25 g).norm.pow 2
  have hk : HasCompactSupport (fun v : ℝ => ‖logLift g.1 v‖ ^ 2) := by
    have hbase := logLift_hasCompactSupport_v25 g
    apply HasCompactSupport.intro hbase
    intro v hv
    have hz : logLift g.1 v = 0 := image_eq_zero_of_notMem_tsupport hv
    simp [hz]
  exact hc.integrable_of_hasCompactSupport hk

theorem shifted_logLift_sq_integrable_v25
    (g : WeilCompactSmoothGV1) (u : ℝ) :
    Integrable (fun v : ℝ => ‖logLift g.1 (v + u)‖ ^ 2) := by
  have hc : Continuous (fun v : ℝ => ‖logLift g.1 (v + u)‖ ^ 2) := by
    exact ((logLift_continuous_v25 g).comp (by fun_prop)).norm.pow 2
  let K : Set ℝ := (fun t : ℝ => t - u) '' tsupport (logLift g.1)
  have hK : IsCompact K :=
    (logLift_hasCompactSupport_v25 g).image (by fun_prop)
  have hk : HasCompactSupport (fun v : ℝ => ‖logLift g.1 (v + u)‖ ^ 2) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro v hv
    have hne : logLift g.1 (v + u) ≠ 0 := by
      intro hz
      apply hv
      simp [hz]
    have hm : v + u ∈ tsupport (logLift g.1) := subset_tsupport _ hne
    refine ⟨v + u, hm, ?_⟩
    ring
  exact hc.integrable_of_hasCompactSupport hk

theorem shifted_logLift_sq_integral_v25
    (g : WeilCompactSmoothGV1) (u : ℝ) :
    (∫ v : ℝ, ‖logLift g.1 (v + u)‖ ^ 2) = energy g.1 := by
  calc
    (∫ v : ℝ, ‖logLift g.1 (v + u)‖ ^ 2)
        = ∫ v : ℝ, ‖logLift g.1 v‖ ^ 2 := by
            simpa using
              (integral_add_right_eq_self
                (fun v : ℝ => ‖logLift g.1 v‖ ^ 2) u)
    _ = energy g.1 := logLift_energy_eq_packet_energy g

theorem logCorrelation_integrable_v25
    (g : WeilCompactSmoothGV1) (u : ℝ) :
    Integrable
      (fun v : ℝ => logLift g.1 (v + u) * conj (logLift g.1 v)) := by
  let M : ℝ → ℝ := fun v =>
    (1 / 2 : ℝ) *
      (‖logLift g.1 (v + u)‖ ^ 2 + ‖logLift g.1 v‖ ^ 2)
  have hM : Integrable M := by
    unfold M
    exact
      ((shifted_logLift_sq_integrable_v25 g u).add
        (logLift_sq_integrable_v25 g)).const_mul (1 / 2 : ℝ)
  have hmeas :
      AEStronglyMeasurable
        (fun v : ℝ => logLift g.1 (v + u) * conj (logLift g.1 v)) := by
    exact
      ((logLift_continuous_v25 g).comp (by fun_prop)).aestronglyMeasurable.mul
        (continuous_conj.comp (logLift_continuous_v25 g)).aestronglyMeasurable
  refine hM.mono' hmeas (Filter.Eventually.of_forall fun v => ?_)
  have hab :
      ‖logLift g.1 (v + u)‖ * ‖logLift g.1 v‖ ≤
        (1 / 2 : ℝ) *
          (‖logLift g.1 (v + u)‖ ^ 2 + ‖logLift g.1 v‖ ^ 2) := by
    nlinarith [sq_nonneg (‖logLift g.1 (v + u)‖ - ‖logLift g.1 v‖)]
  simpa [M, norm_mul, norm_conj] using hab

/-- Exact multiplicative-to-additive autocorrelation identity. -/
theorem logCorrelation_eq_autocorrelation_v25
    (g : WeilCompactSmoothGV1) (u : ℝ) :
    logCorrelationV25 g u =
      (Real.exp (u / 2) : ℂ) *
        WeilAutocorrelationV1 g (Real.exp u) := by
  unfold logCorrelationV25 WeilAutocorrelationV1
  rw [AEGIS.WeilThreeBlockTranslatedPacketsV22.integral_exp_substitution_complex]
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
    (Real.exp ((v + u) / 2) : ℂ) * g.1 (Real.exp (v + u)) *
        ((Real.exp (v / 2) : ℂ) * conj (g.1 (Real.exp v)))
        =
      ((Real.exp ((v + u) / 2) : ℂ) *
          (Real.exp (v / 2) : ℂ)) *
        (g.1 (Real.exp (v + u)) * conj (g.1 (Real.exp v))) := by ring
    _ =
      ((Real.exp (u / 2) : ℂ) * (Real.exp v : ℂ)) *
        (g.1 (Real.exp (v + u)) * conj (g.1 (Real.exp v))) := by
          rw [← hscalar]
    _ =
      (Real.exp (u / 2) : ℂ) *
        ((Real.exp v : ℂ) *
          (g.1 (Real.exp (v + u)) * conj (g.1 (Real.exp v)))) := by ring

/-- The L2 autocorrelation is bounded by the packet energy.  This uses only
2ab <= a^2+b^2, avoiding any additional Hilbert-space API. -/
theorem norm_logCorrelation_le_energy_v25
    (g : WeilCompactSmoothGV1) (u : ℝ) :
    ‖logCorrelationV25 g u‖ ≤ energy g.1 := by
  let q : ℝ → ℂ := fun v =>
    logLift g.1 (v + u) * conj (logLift g.1 v)
  let M : ℝ → ℝ := fun v =>
    (1 / 2 : ℝ) *
      (‖logLift g.1 (v + u)‖ ^ 2 + ‖logLift g.1 v‖ ^ 2)
  have hq : Integrable q := by
    simpa [q] using logCorrelation_integrable_v25 g u
  have hM : Integrable M := by
    unfold M
    exact
      ((shifted_logLift_sq_integrable_v25 g u).add
        (logLift_sq_integrable_v25 g)).const_mul (1 / 2 : ℝ)
  have hpoint : ∀ v : ℝ, ‖q v‖ ≤ M v := by
    intro v
    have hab :
        ‖logLift g.1 (v + u)‖ * ‖logLift g.1 v‖ ≤
          (1 / 2 : ℝ) *
            (‖logLift g.1 (v + u)‖ ^ 2 + ‖logLift g.1 v‖ ^ 2) := by
      nlinarith [sq_nonneg (‖logLift g.1 (v + u)‖ - ‖logLift g.1 v‖)]
    simpa [q, M, norm_mul, norm_conj] using hab
  calc
    ‖logCorrelationV25 g u‖
        = ‖∫ v : ℝ, q v‖ := by rfl
    _ ≤ ∫ v : ℝ, ‖q v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v : ℝ, M v := by
      exact integral_mono hq.norm hM hpoint
    _ = (1 / 2 : ℝ) *
        ((∫ v : ℝ, ‖logLift g.1 (v + u)‖ ^ 2) +
          ∫ v : ℝ, ‖logLift g.1 v‖ ^ 2) := by
      unfold M
      rw [integral_const_mul, integral_add
        (shifted_logLift_sq_integrable_v25 g u)
        (logLift_sq_integrable_v25 g)]
    _ = energy g.1 := by
      rw [shifted_logLift_sq_integral_v25,
        logLift_energy_eq_packet_energy]
      ring

/-- Width-1/32 support makes the additive autocorrelation vanish strictly
outside the difference-support interval. -/
theorem logCorrelation_zero_of_width_v25
    (g : WeilCompactSmoothGV1) (a u : ℝ)
    (hw : WidthOneThirtyTwoAt g a)
    (hu : (1 / 32 : ℝ) < u) :
    logCorrelationV25 g u = 0 := by
  unfold logCorrelationV25
  apply integral_eq_zero_of_ae
  filter_upwards [] with v
  by_cases h0 : logLift g.1 v = 0
  · simp [h0]
  · by_cases h1 : logLift g.1 (v + u) = 0
    · simp [h1]
    · have hm0 : v ∈ tsupport (logLift g.1) := subset_tsupport _ h0
      have hm1 : v + u ∈ tsupport (logLift g.1) := subset_tsupport _ h1
      have hv := hw hm0
      have hvu := hw hm1
      exfalso
      linarith [hv.1, hv.2, hvu.1, hvu.2, hu]

end AEGIS.WeilWidthArchCorrelationV25

#print axioms AEGIS.WeilWidthArchCorrelationV25.logLift_sq_integrable_v25
#print axioms AEGIS.WeilWidthArchCorrelationV25.logCorrelation_eq_autocorrelation_v25
#print axioms AEGIS.WeilWidthArchCorrelationV25.norm_logCorrelation_le_energy_v25
#print axioms AEGIS.WeilWidthArchCorrelationV25.logCorrelation_zero_of_width_v25
