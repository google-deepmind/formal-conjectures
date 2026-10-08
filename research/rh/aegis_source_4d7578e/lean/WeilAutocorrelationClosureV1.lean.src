import WeilArchimedeanConvergenceV1
import WeilAutocorrelationRealityV1
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Tactic

/-!
Closure of the existing Lebesgue-measure Weil autocorrelation in the existing
compact-smooth positive-support class. The integral and normalization are unchanged.

The support envelope consists of ratios of points of `tsupport g`. Smoothness
uses the fixed compact support of the second factor in the integration variable.
Arithmetic convergence then follows from the existing compact-smooth theorem.

EXPLICIT_FORMULA_OPEN
ARITHMETIC_NEGATIVITY_OPEN
FULL_WEIL_CLASS_COVERAGE_OPEN
RH_EQUIVALENCE_OPEN
RH_NOT_PROVEN
-/

open Set Function MeasureTheory Complex
open scoped ContDiff Convolution ComplexConjugate

set_option autoImplicit false

noncomputable section

/-- A compact ratio envelope; this does not assert equality with the support. -/
def WeilAutocorrelationSupportEnvelopeV1 (g : WeilCompactSmoothGV1) : Set ℝ :=
  (fun p : ℝ × ℝ => p.1 / p.2) '' (tsupport g.1 ×ˢ tsupport g.1)

theorem weil_autocorrelation_support_envelope_compact_v1 (g : WeilCompactSmoothGV1) :
    IsCompact (WeilAutocorrelationSupportEnvelopeV1 g) := by
  apply (g.2.2.1.prod g.2.2.1).image_of_continuousOn
  exact continuous_fst.continuousOn.div continuous_snd.continuousOn
    (fun p hp => ne_of_gt (g.2.2.2 hp.2))

theorem weil_autocorrelation_support_envelope_positive_v1 (g : WeilCompactSmoothGV1) :
    WeilAutocorrelationSupportEnvelopeV1 g ⊆ Ioi 0 := by
  rintro x ⟨p, hp, rfl⟩
  change 0 < p.1 / p.2
  exact div_pos (show 0 < p.1 from g.2.2.2 hp.1)
    (show 0 < p.2 from g.2.2.2 hp.2)

/-- The integrand vanishes unless both arguments lie in the original support. -/
theorem weil_autocorrelation_tsupport_subset_v1 (g : WeilCompactSmoothGV1) :
    tsupport (WeilAutocorrelationV1 g) ⊆ WeilAutocorrelationSupportEnvelopeV1 g := by
  apply closure_minimal ?_ (weil_autocorrelation_support_envelope_compact_v1 g).isClosed
  intro x hx
  by_contra hnot
  apply hx
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : g.1 y = 0
  · simp [hy]
  · have hyK : y ∈ tsupport g.1 := subset_tsupport g.1 hy
    have hxy : g.1 (x * y) = 0 := by
      by_contra hxy
      apply hnot
      refine ⟨(x * y, y), ⟨subset_tsupport g.1 hxy, hyK⟩, ?_⟩
      exact mul_div_cancel_right₀ x (ne_of_gt (g.2.2.2 hyK))
    simp [hxy]

theorem weil_autocorrelation_hasCompactSupport_v1 (g : WeilCompactSmoothGV1) :
    HasCompactSupport (WeilAutocorrelationV1 g) :=
  (weil_autocorrelation_support_envelope_compact_v1 g).of_isClosed_subset
    (isClosed_tsupport _) (weil_autocorrelation_tsupport_subset_v1 g)

theorem weil_autocorrelation_tsupport_positive_v1 (g : WeilCompactSmoothGV1) :
    tsupport (WeilAutocorrelationV1 g) ⊆ Ioi 0 :=
  (weil_autocorrelation_tsupport_subset_v1 g).trans
    (weil_autocorrelation_support_envelope_positive_v1 g)

/-- Pointwise existence of the actual autocorrelation integral, independently
of the convention that Lean assigns values to nonintegrable integrals. -/
theorem weil_autocorrelation_integrand_integrable_v1 (g : WeilCompactSmoothGV1) (x : ℝ) :
    IntegrableOn (fun y : ℝ => g.1 (x * y) * star (g.1 y)) (Ioi 0) := by
  have hc : Continuous (fun y : ℝ => g.1 (x * y) * star (g.1 y)) := by
    exact (g.2.1.continuous.comp (continuous_const.mul continuous_id)).mul
      (continuous_star.comp g.2.1.continuous)
  have hk : HasCompactSupport (fun y : ℝ => g.1 (x * y) * star (g.1 y)) := by
    apply HasCompactSupport.intro g.2.2.1
    intro y hy
    simp [image_eq_zero_of_notMem_tsupport hy]
  exact (hc.integrable_of_hasCompactSupport hk).integrableOn

/-- Smoothness follows from a fixed compact support in the integration variable.
The auxiliary convolution is evaluated at zero and rewrites exactly to the
original integral with measure `volume.restrict (Ioi 0)`. -/
theorem weil_autocorrelation_contDiff_v1 (g : WeilCompactSmoothGV1) :
    ContDiff ℝ ∞ (WeilAutocorrelationV1 g) := by
  let F : ℝ → ℝ → ℂ := fun p z => g.1 (p * (-z)) * conj (g.1 (-z))
  have hF : ContDiff ℝ ∞ (fun q : ℝ × ℝ => F q.1 q.2) :=
    (g.2.1.comp (contDiff_fst.mul contDiff_snd.neg)).mul
      (Complex.conjCLE.contDiff.comp (g.2.1.comp contDiff_snd.neg))
  have hsupport : ∀ p z : ℝ, p ∈ (univ : Set ℝ) →
      z ∉ (fun y : ℝ => -y) '' tsupport g.1 → F p z = 0 := by
    intro p z _ hz
    have hneg : -z ∉ tsupport g.1 := by
      intro h
      exact hz ⟨-z, h, neg_neg z⟩
    simp [F, image_eq_zero_of_notMem_tsupport hneg]
  have H := contDiffOn_convolution_right_with_param_comp
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (v := fun _ : ℝ => (0 : ℝ)) (n := (⊤ : ℕ∞)) contDiffOn_const
    isOpen_univ (g.2.2.1.image continuous_neg) hsupport
    (locallyIntegrable_const (μ := volume.restrict (Ioi (0 : ℝ))) (1 : ℝ))
    hF.contDiffOn
  rw [← contDiffOn_univ]
  change ContDiffOn ℝ ∞
    (fun x : ℝ => ∫ y in Ioi (0 : ℝ), g.1 (x * y) * star (g.1 y)) univ
  simpa only [convolution, F, zero_sub, neg_neg,
    ContinuousLinearMap.lsmul_apply, one_smul,
    Complex.star_def] using H

/-- Repackage the original function with proved class membership. -/
def WeilAutocorrelationCompactSmoothV1 (g : WeilCompactSmoothGV1) : WeilCompactSmoothGV1 :=
  ⟨WeilAutocorrelationV1 g, weil_autocorrelation_contDiff_v1 g,
    weil_autocorrelation_hasCompactSupport_v1 g, weil_autocorrelation_tsupport_positive_v1 g⟩

theorem weil_autocorrelation_compact_smooth_coe_v1 (g : WeilCompactSmoothGV1) :
    (WeilAutocorrelationCompactSmoothV1 g).1 = WeilAutocorrelationV1 g := rfl

/-- Discharge the convergence premise using the unchanged arithmetic theorem. -/
theorem weil_autocorrelation_explicit_right_side_convergent_v1 (g : WeilCompactSmoothGV1) :
    WeilExplicitRightSideConvergentV1 (WeilAutocorrelationV1 g) :=
  weil_compact_smooth_explicit_right_side_convergent_v1
    (WeilAutocorrelationCompactSmoothV1 g)

/-- The original candidate is equivalent to its remaining real sign inequality.
Neither that inequality nor the candidate is asserted here. -/
theorem weil_compact_smooth_negativity_iff_unconditional_real_inequality_v1 :
    WeilCompactSmoothNegativityV1 ↔
      ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
        (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 := by
  rw [weil_compact_smooth_negativity_iff_real_inequality_v1]
  constructor
  · intro h g hm
    exact h g hm (weil_autocorrelation_explicit_right_side_convergent_v1 g)
  · intro h g hm _
    exact h g hm

#print axioms weil_autocorrelation_support_envelope_compact_v1
#print axioms weil_autocorrelation_support_envelope_positive_v1
#print axioms weil_autocorrelation_tsupport_subset_v1
#print axioms weil_autocorrelation_hasCompactSupport_v1
#print axioms weil_autocorrelation_tsupport_positive_v1
#print axioms weil_autocorrelation_integrand_integrable_v1
#print axioms weil_autocorrelation_contDiff_v1
#print axioms weil_autocorrelation_compact_smooth_coe_v1
#print axioms weil_autocorrelation_explicit_right_side_convergent_v1
#print axioms weil_compact_smooth_negativity_iff_unconditional_real_inequality_v1
