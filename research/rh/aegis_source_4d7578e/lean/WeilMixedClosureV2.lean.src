import WeilAutocorrelationClosureV1

/-!
Actual mixed multiplicative correlation, with the repository's dy normalization.
This closes support, smoothness, integral existence, and arithmetic convergence.
It does NOT prove the logarithmic kernel identity or any sign estimate.
-/
open Set Function MeasureTheory Complex
open scoped ContDiff Convolution ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace AEGIS.WeilMixedClosureV2

def mixed (a b : WeilCompactSmoothGV1) (x : ℝ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), a.1 (x * y) * star (b.1 y)

def envelope (a b : WeilCompactSmoothGV1) : Set ℝ :=
  (fun p : ℝ × ℝ => p.1 / p.2) '' (tsupport a.1 ×ˢ tsupport b.1)

theorem diagonal_eq (a : WeilCompactSmoothGV1) : mixed a a = WeilAutocorrelationV1 a := rfl

theorem envelope_compact (a b : WeilCompactSmoothGV1) : IsCompact (envelope a b) := by
  apply (a.2.2.1.prod b.2.2.1).image_of_continuousOn
  exact continuous_fst.continuousOn.div continuous_snd.continuousOn
    (fun p hp => ne_of_gt (b.2.2.2 hp.2))

theorem envelope_positive (a b : WeilCompactSmoothGV1) : envelope a b ⊆ Ioi 0 := by
  rintro x ⟨p, hp, rfl⟩
  change 0 < p.1 / p.2
  exact div_pos (show 0 < p.1 from a.2.2.2 hp.1)
    (show 0 < p.2 from b.2.2.2 hp.2)

theorem support_subset (a b : WeilCompactSmoothGV1) : tsupport (mixed a b) ⊆ envelope a b := by
  apply closure_minimal ?_ (envelope_compact a b).isClosed
  intro x hx
  by_contra hnot
  apply hx
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : b.1 y = 0
  · simp [hy]
  · have hyK : y ∈ tsupport b.1 := subset_tsupport b.1 hy
    have hxy : a.1 (x * y) = 0 := by
      by_contra hxy
      apply hnot
      refine ⟨(x * y, y), ⟨subset_tsupport a.1 hxy, hyK⟩, ?_⟩
      exact mul_div_cancel_right₀ x (ne_of_gt (b.2.2.2 hyK))
    simp [hxy]

theorem compact_support (a b : WeilCompactSmoothGV1) : HasCompactSupport (mixed a b) :=
  (envelope_compact a b).of_isClosed_subset (isClosed_tsupport _) (support_subset a b)

theorem positive_support (a b : WeilCompactSmoothGV1) : tsupport (mixed a b) ⊆ Ioi 0 :=
  (support_subset a b).trans (envelope_positive a b)

theorem integrand_integrable (a b : WeilCompactSmoothGV1) (x : ℝ) :
    IntegrableOn (fun y : ℝ => a.1 (x * y) * star (b.1 y)) (Ioi 0) := by
  have hc : Continuous (fun y : ℝ => a.1 (x * y) * star (b.1 y)) :=
    (a.2.1.continuous.comp (continuous_const.mul continuous_id)).mul
      (continuous_star.comp b.2.1.continuous)
  have hk : HasCompactSupport (fun y : ℝ => a.1 (x * y) * star (b.1 y)) := by
    apply HasCompactSupport.intro b.2.2.1
    intro y hy
    simp [image_eq_zero_of_notMem_tsupport hy]
  exact (hc.integrable_of_hasCompactSupport hk).integrableOn

theorem smooth (a b : WeilCompactSmoothGV1) : ContDiff ℝ ∞ (mixed a b) := by
  let F : ℝ → ℝ → ℂ := fun p z => a.1 (p * (-z)) * conj (b.1 (-z))
  have hF : ContDiff ℝ ∞ (fun q : ℝ × ℝ => F q.1 q.2) :=
    (a.2.1.comp (contDiff_fst.mul contDiff_snd.neg)).mul
      (Complex.conjCLE.contDiff.comp (b.2.1.comp contDiff_snd.neg))
  have hsupport : ∀ p z : ℝ, p ∈ (univ : Set ℝ) →
      z ∉ (fun y : ℝ => -y) '' tsupport b.1 → F p z = 0 := by
    intro p z _ hz
    have hneg : -z ∉ tsupport b.1 := by
      intro h
      exact hz ⟨-z, h, neg_neg z⟩
    simp [F, image_eq_zero_of_notMem_tsupport hneg]
  have H := contDiffOn_convolution_right_with_param_comp
    (μ := volume.restrict (Ioi (0 : ℝ))) (ContinuousLinearMap.lsmul ℝ ℝ)
    (v := fun _ : ℝ => (0 : ℝ)) (n := (⊤ : ℕ∞)) contDiffOn_const
    isOpen_univ (b.2.2.1.image continuous_neg) hsupport
    (locallyIntegrable_const (μ := volume.restrict (Ioi (0 : ℝ))) (1 : ℝ))
    hF.contDiffOn
  rw [← contDiffOn_univ]
  change ContDiffOn ℝ ∞
    (fun x : ℝ => ∫ y in Ioi (0 : ℝ), a.1 (x * y) * star (b.1 y)) univ
  simpa only [convolution, F, zero_sub, neg_neg,
    ContinuousLinearMap.lsmul_apply, one_smul, Complex.star_def] using H

def asPacket (a b : WeilCompactSmoothGV1) : WeilCompactSmoothGV1 :=
  ⟨mixed a b, smooth a b, compact_support a b, positive_support a b⟩

theorem asPacket_coe (a b : WeilCompactSmoothGV1) : (asPacket a b).1 = mixed a b := rfl

theorem rhs_convergent (a b : WeilCompactSmoothGV1) :
    WeilExplicitRightSideConvergentV1 (mixed a b) :=
  weil_compact_smooth_explicit_right_side_convergent_v1 (asPacket a b)

/-- This is an identity for the actual mixed integral, not a new normalization. -/
theorem reciprocal (a b : WeilCompactSmoothGV1) {x : ℝ} (hx : 0 < x) :
    mixed a b x⁻¹ = (x : ℂ) * conj (mixed b a x) := by
  have hchange := integral_comp_mul_left_Ioi'
    (fun y : ℝ => a.1 (x⁻¹ * y) * conj (b.1 y)) 0 hx
  simp only [mul_zero, inv_mul_cancel_left₀ hx.ne'] at hchange
  have hconj : (∫ y in Ioi (0 : ℝ), a.1 y * conj (b.1 (x * y))) =
      conj (∫ y in Ioi (0 : ℝ), b.1 (x * y) * conj (a.1 y)) := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with y
    simp [mul_comm]
  simpa only [mixed, Complex.star_def, hconj, Complex.real_smul] using hchange.symm

end AEGIS.WeilMixedClosureV2
