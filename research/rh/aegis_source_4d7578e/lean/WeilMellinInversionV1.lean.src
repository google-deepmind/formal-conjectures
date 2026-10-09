import MellinDecayEstimateV1
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
Mellin convergence and inversion for the existing compact smooth positive
support class, on every real vertical line. The pinned cubic-decay source is
unchanged; this extension reuses its canonical logarithmic profile definitions.
-/

open Set Filter Topology Complex MeasureTheory
open scoped ContDiff FourierTransform

noncomputable section

private theorem mellin_log_profile_contDiff_v1 (g : WeilCompactSmoothGV1) :
    ContDiff ℝ ∞ (MellinLogProfileV1 g.1) := by
  unfold MellinLogProfileV1
  have hneg : ContDiff ℝ ∞ (fun u : ℝ => -u) := by fun_prop
  exact g.2.1.comp (Real.contDiff_exp.comp hneg)

private theorem mellin_log_profile_hasCompactSupport_v1
    (g : WeilCompactSmoothGV1) :
    HasCompactSupport (MellinLogProfileV1 g.1) := by
  let K : Set ℝ := (fun x : ℝ => -Real.log x) '' tsupport g.1
  have hts : IsCompact (tsupport g.1) := by
    change IsCompact (closure (Function.support g.1))
    exact g.2.2.1
  have hlog : ContinuousOn (fun x : ℝ => -Real.log x) (tsupport g.1) := by
    intro x hx
    have hxpos : 0 < x := g.2.2.2 hx
    exact (Real.continuousAt_log hxpos.ne').neg.continuousWithinAt
  have hK : IsCompact K := hts.image_of_continuousOn hlog
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro u hu
  change g.1 (Real.exp (-u)) ≠ 0 at hu
  have hmem : Real.exp (-u) ∈ tsupport g.1 := subset_closure hu
  refine ⟨Real.exp (-u), hmem, ?_⟩
  simp

private theorem mellin_weight_contDiff_v1 (σ : ℝ) :
    ContDiff ℝ ∞ (MellinWeightV1 σ) := by
  unfold MellinWeightV1
  fun_prop

private theorem mellin_complex_weight_contDiff_v1 (σ : ℝ) :
    ContDiff ℝ ∞ (MellinComplexWeightV1 σ) := by
  unfold MellinComplexWeightV1
  exact (mellin_weight_contDiff_v1 σ).smul_const (1 : ℂ)

private theorem mellin_weighted_log_profile_contDiff_v1
    (g : WeilCompactSmoothGV1) (σ : ℝ) :
    ContDiff ℝ ∞ (MellinWeightedLogProfileV1 g.1 σ) := by
  unfold MellinWeightedLogProfileV1
  exact (mellin_complex_weight_contDiff_v1 σ).mul (mellin_log_profile_contDiff_v1 g)

private theorem mellin_weighted_log_profile_hasCompactSupport_v1
    (g : WeilCompactSmoothGV1) (σ : ℝ) :
    HasCompactSupport (MellinWeightedLogProfileV1 g.1 σ) := by
  have hh : HasCompactSupport (MellinLogProfileV1 g.1) :=
    mellin_log_profile_hasCompactSupport_v1 g
  apply hh.of_isClosed_subset (isClosed_tsupport _)
  change tsupport (fun u : ℝ =>
      MellinComplexWeightV1 σ u * MellinLogProfileV1 g.1 u) ⊆
    tsupport (MellinLogProfileV1 g.1)
  exact tsupport_mul_subset_right


set_option autoImplicit false

/-- Compact positive support gives Mellin convergence at every complex point.
This reuses the existing test-function carrier and the ordinary Mellin integral. -/
theorem weil_compact_smooth_mellin_convergent_all_v1
    (f : WeilCompactSmoothGV1) (s : ℂ) :
    MellinConvergent f.1 s := by
  rw [MellinConvergent]
  let q : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * f.1 t
  have hq_on : ContinuousOn q (Set.Ioi 0) := by
    intro t ht
    exact
      (continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_gt ht)).continuousWithinAt.mul
        f.2.1.continuous.continuousAt.continuousWithinAt
  have hq_ts : tsupport q ⊆ Set.Ioi 0 :=
    (tsupport_mul_subset_right
      (f := fun t : ℝ => (t : ℂ) ^ (s - 1)) (g := f.1)).trans f.2.2.2
  have hq_cont : Continuous q :=
    hq_on.continuous_of_tsupport_subset isOpen_Ioi hq_ts
  have hq_compact : HasCompactSupport q := f.2.2.1.mul_left
  simpa only [q, smul_eq_mul] using
    (hq_cont.integrable_of_hasCompactSupport hq_compact).integrableOn

/-- Every fixed vertical line is integrable. Compact-smooth logarithmic
profiles are Schwartz, so no restriction to the critical strip is needed. -/
theorem weil_compact_smooth_mellin_vertical_integrable_all_v1
    (f : WeilCompactSmoothGV1) (σ : ℝ) :
    VerticalIntegrable (mellin f.1) σ := by
  let p := MellinWeightedLogProfileV1 f.1 σ
  let P : SchwartzMap ℝ ℂ :=
    (mellin_weighted_log_profile_hasCompactSupport_v1 f σ).toSchwartzMap
      (mellin_weighted_log_profile_contDiff_v1 f σ)
  have hFourier : Integrable (𝓕 p) := by
    exact (𝓕 P).integrable
  have hscaled := hFourier.comp_mul_right'
    (inv_ne_zero (show 2 * Real.pi ≠ 0 by positivity))
  have hmellin (γ : ℝ) :
      mellin f.1 ((σ : ℂ) + (γ : ℂ) * Complex.I) =
        𝓕 p (γ / (2 * Real.pi)) := by
    rw [mellin_eq_fourier]
    have hre : (((σ : ℂ) + (γ : ℂ) * Complex.I).re) = σ := by simp
    have him : (((σ : ℂ) + (γ : ℂ) * Complex.I).im) = γ := by simp
    rw [hre, him]
    have hprofile :
        (fun u : ℝ => Real.exp (-σ * u) • f.1 (Real.exp (-u))) = p := by
      funext u
      simp [p, MellinWeightedLogProfileV1, MellinComplexWeightV1,
        MellinWeightV1, MellinLogProfileV1, Complex.real_smul]
    rw [hprofile]
  change Integrable (fun γ : ℝ => mellin f.1 ((σ : ℂ) + (γ : ℂ) * Complex.I))
  simpa only [hmellin, div_eq_mul_inv] using hscaled

/-- Mellin inversion on every real vertical line, with all analytic hypotheses
discharged by the existing compact-smooth positive-support class. -/
theorem weil_compact_smooth_mellin_inversion_v1
    (f : WeilCompactSmoothGV1) (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ (mellin f.1) x = f.1 x := by
  exact mellinInv_mellin_eq σ f.1 hx
    (weil_compact_smooth_mellin_convergent_all_v1 f σ)
    (weil_compact_smooth_mellin_vertical_integrable_all_v1 f σ)
    f.2.1.continuous.continuousAt
