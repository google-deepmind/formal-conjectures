/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import RHRestrictedWeilBridgeV13

/-!
# A detecting packet criterion for the actual Riemann Hypothesis

This specializes the source resolvent argument to one packet whose zero
coefficients never vanish. A uniform bound for this packet's translated
zero kernel gives a holomorphic Laplace transform on the right half-plane.
A right-hand zero would then be a nonremovable pole of that transform.

The analytic proof bodies are parameterized from
`RHZeroKernelLaplaceAnalyticV12` and `RHRestrictedWeilBridgeV13` at AEGIS source
`2c3d041b633147ec97c7ef753aa9d157a47bb9f5`. Separation, connectedness,
resolvent analyticity, and the pole contradiction are imported unchanged.
The only sign-related premise here is the stated bound for one packet.
-/

open Set Filter Topology Complex MeasureTheory
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHDetectingPacketCriterionV1

open AEGIS.WeilZeroTwoPointV11
open AEGIS.RHZeroKernelLaplaceV12
open AEGIS.RHZeroKernelLaplaceAnalyticV12
open AEGIS.RHRestrictedWeilBridgeV13
open AEGIS.RestrictedWeilCriterionFinalV13

/-- A uniform norm bound for the translated zero kernel of one fixed packet. -/
def PacketKernelBoundV1 (g : WeilCompactSmoothGV1) : Prop :=
  ∃ C : ℝ, ∀ t : ℝ, ‖WeilZeroTranslationKernelV11 g t‖ ≤ C

/-- The bounded zero kernel has an integrable Laplace transform for every
parameter in Re(w)>0. -/
theorem zero_kernel_laplace_integrable_of_bound
    (g : WeilCompactSmoothGV1) (C : ℝ)
    (hK : ∀ t : ℝ, ‖WeilZeroTranslationKernelV11 g t‖ ≤ C)
    (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        Complex.exp (-(w * (t : ℂ))) *
          WeilZeroTranslationKernelV11 g t)
      (Ioi (0 : ℝ)) := by
  let B : ℝ := C
  have hmajor :
      IntegrableOn
        (fun t : ℝ => B * Real.exp (-w.re * t))
        (Ioi (0 : ℝ)) := by
    exact
      (integrableOn_exp_mul_Ioi (a := -w.re) (by linarith) 0).const_mul B
  have hmeas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          Complex.exp (-(w * (t : ℂ))) *
            WeilZeroTranslationKernelV11 g t)
        (volume.restrict (Ioi (0 : ℝ))) := by
    exact
      ((by fun_prop :
        Continuous (fun t : ℝ =>
          Complex.exp (-(w * (t : ℂ))))).aestronglyMeasurable.mul
        (zero_translation_kernel_continuous_v12 g).aestronglyMeasurable).restrict
  refine hmajor.mono' hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact Filter.Eventually.of_forall (fun t ht => by
    rw [norm_mul, Complex.norm_exp]
    have hK := hK t
    have hre :
        (-(w * (t : ℂ))).re = -w.re * t := by
      simp
    rw [hre, mul_comm B]
    exact mul_le_mul_of_nonneg_left hK (Real.exp_nonneg _))

/-- An integrable first-moment exponential tail used to dominate the
w-derivative locally. -/
private theorem first_moment_exp_tail_integrable_v12
    (δ B : ℝ) (hδ : 0 < δ) :
    IntegrableOn
      (fun t : ℝ => B * (t * Real.exp (-(δ * t))))
      (Ioi (0 : ℝ)) := by
  by_cases hB : B = 0
  · simp [hB]
  have hbase :
      IntegrableOn
        (fun t : ℝ => t * Real.exp (-(δ * t)))
        (Ioi (0 : ℝ)) := by
    have hI :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := δ)
        (by norm_num) (by norm_num) hδ
    refine hI.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [Real.rpow_one]
  exact hbase.const_mul B

/-- Differentiability of the bounded-kernel Laplace transform at every point
of the open right half-plane. -/
theorem zero_kernel_laplace_differentiableAt_of_bound
    (g : WeilCompactSmoothGV1) (C : ℝ)
    (hK : ∀ t : ℝ, ‖WeilZeroTranslationKernelV11 g t‖ ≤ C)
    (w0 : ℂ) (hw0 : 0 < w0.re) :
    DifferentiableAt ℂ (WeilZeroKernelLaplaceV12 g) w0 := by
  let δ : ℝ := w0.re / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let B : ℝ := C
  have hB : 0 ≤ C := (norm_nonneg (WeilZeroTranslationKernelV11 g 0)).trans (hK 0)

  let F : ℂ → ℝ → ℂ := fun w t =>
    Complex.exp (-(w * (t : ℂ))) *
      WeilZeroTranslationKernelV11 g t
  let F' : ℂ → ℝ → ℂ := fun w t =>
    (-(t : ℂ)) *
      Complex.exp (-(w * (t : ℂ))) *
        WeilZeroTranslationKernelV11 g t
  let bound : ℝ → ℝ := fun t =>
    B * (t * Real.exp (-(δ * t)))

  have hs : Metric.ball w0 δ ∈ 𝓝 w0 :=
    Metric.ball_mem_nhds _ hδ

  have hFmeas :
      ∀ᶠ w in 𝓝 w0,
        AEStronglyMeasurable (F w)
          (volume.restrict (Ioi (0 : ℝ))) := by
    exact Filter.Eventually.of_forall (fun w => by
      apply AEStronglyMeasurable.restrict
      exact
        ((by fun_prop :
          Continuous (fun t : ℝ =>
            Complex.exp (-(w * (t : ℂ))))).aestronglyMeasurable.mul
          (zero_translation_kernel_continuous_v12 g).aestronglyMeasurable))

  have hFint :
      Integrable (F w0) (volume.restrict (Ioi (0 : ℝ))) := by
    exact zero_kernel_laplace_integrable_of_bound
      g C hK w0 hw0

  have hF'meas :
      AEStronglyMeasurable (F' w0)
        (volume.restrict (Ioi (0 : ℝ))) := by
    apply AEStronglyMeasurable.restrict
    exact
      ((by fun_prop :
        Continuous (fun t : ℝ =>
          (-(t : ℂ)) *
            Complex.exp (-(w0 * (t : ℂ))))).aestronglyMeasurable.mul
        (zero_translation_kernel_continuous_v12 g).aestronglyMeasurable)

  have hbound :
      ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
        ∀ w ∈ Metric.ball w0 δ, ‖F' w t‖ ≤ bound t := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun t ht w hw => by
      have ht0 : 0 ≤ t := le_of_lt ht
      have hdist : ‖w - w0‖ < δ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hw
      have hreDiff : |w.re - w0.re| ≤ ‖w - w0‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - w0)
      have hwre : δ ≤ w.re := by
        have hlo := (abs_lt.mp (lt_of_le_of_lt hreDiff hdist)).1
        dsimp only [δ] at hlo ⊢
        linarith
      have hK := hK t
      simp only [F', bound, B]
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ht0, Complex.norm_exp]
      have hre :
          (-(w * (t : ℂ))).re = -w.re * t := by
        simp
      rw [hre]
      have hexp :
          Real.exp (-w.re * t) ≤ Real.exp (-(δ * t)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      calc
        t * Real.exp (-w.re * t) *
            ‖WeilZeroTranslationKernelV11 g t‖
          ≤ t * Real.exp (-(δ * t)) *
              (C) := by
              gcongr
        _ = C *
              (t * Real.exp (-(δ * t))) := by ring)

  have hboundInt :
      Integrable bound (volume.restrict (Ioi (0 : ℝ))) := by
    exact first_moment_exp_tail_integrable_v12 δ B hδ

  have hdiff :
      ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
        ∀ w ∈ Metric.ball w0 δ,
          HasDerivAt (F · t) (F' w t) w := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun t ht w hw => by
      simp only [F, F']
      have hinner :
          HasDerivAt (fun z : ℂ => -(z * (t : ℂ))) (-(t : ℂ)) w :=
        (hasDerivAt_mul_const (t : ℂ)).neg
      have hExp :
          HasDerivAt
            (fun z : ℂ => Complex.exp (-(z * (t : ℂ))))
            (-(t : ℂ) *
              Complex.exp (-(w * (t : ℂ)))) w :=
        hinner.cexp.congr_deriv (by ring)
      exact hExp.mul_const
        (WeilZeroTranslationKernelV11 g t))

  have main :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := F) (F' := F') (bound := bound)
      hs hFmeas hFint hF'meas hbound hboundInt hdiff

  exact main.2.differentiableAt

/-- Under a bound for this single packet, its Laplace transform is holomorphic on the
entire open right half-plane. -/
theorem zero_kernel_laplace_analyticOnNhd_of_bound
    (g : WeilCompactSmoothGV1) (C : ℝ)
    (hK : ∀ t : ℝ, ‖WeilZeroTranslationKernelV11 g t‖ ≤ C) :
    AnalyticOnNhd ℂ
      (WeilZeroKernelLaplaceV12 g)
      ZeroLaplaceRightHalfPlaneV12 := by
  apply DifferentiableOn.analyticOnNhd
  · intro w hw
    exact
      (zero_kernel_laplace_differentiableAt_of_bound
        g C hK w hw).differentiableWithinAt
  · exact zeroLaplaceRightHalfPlane_isOpen_v12

theorem laplace_eq_resolvent_on_domain_of_bound
    (g : WeilCompactSmoothGV1) (C : ℝ)
    (hK : ∀ t : ℝ, ‖WeilZeroTranslationKernelV11 g t‖ ≤ C) :
    EqOn (WeilZeroKernelLaplaceV12 g) (WeilZeroResolventV12 g) BridgeDomainV13 := by
  have hL : AnalyticOnNhd ℂ (WeilZeroKernelLaplaceV12 g) BridgeDomainV13 :=
    (zero_kernel_laplace_analyticOnNhd_of_bound g C hK).mono (fun w hw => hw.1)
  have hR : AnalyticOnNhd ℂ (WeilZeroResolventV12 g) BridgeDomainV13 := by
    intro w hw
    obtain ⟨ε, hε, hsep⟩ :=
      exists_sep_of_not_centered_zero_v13 w hw.1 (fun rho heq => hw.2 ⟨rho, heq⟩)
    rw [resolvent_eq_resolventSum_v13]
    exact resolventSum_analyticAt_v13 (WeilZeroCoefficientV11 g)
      (zero_coefficient_norm_summable_v12 g) w hε (fun rho _ => hsep rho)
  refine hL.eqOn_of_preconnected_of_eventuallyEq hR bridgeDomain_isPreconnected_v13
    one_mem_bridgeDomain_v13 ?_
  have hopen : IsOpen {w : ℂ | (1 / 2 : ℝ) < w.re} :=
    Complex.continuous_re.isOpen_preimage (Ioi (1 / 2 : ℝ)) isOpen_Ioi
  have hmem : {w : ℂ | (1 / 2 : ℝ) < w.re} ∈ 𝓝 (1 : ℂ) :=
    hopen.mem_nhds (by simp; norm_num)
  filter_upwards [hmem] with w hw
  exact zero_kernel_laplace_eq_resolvent_v12 g w hw

/-! ### The pole contradiction -/

theorem zero_re_le_half_of_detecting_kernel_bound
    (g : WeilCompactSmoothGV1) (C : ℝ)
    (hK : ∀ t : ℝ, ‖WeilZeroTranslationKernelV11 g t‖ ≤ C)
    (rho0 : RiemannNontrivialZeroIndexV2)
    (ha : WeilZeroCoefficientV11 g rho0 ≠ 0) :
    rho0.1.re ≤ 1 / 2 := by
  by_contra hlt
  have hlt' : 1 / 2 < rho0.1.re := lt_of_not_ge hlt
  set z : ℂ := WeilCenteredZeroExponentV12 rho0 with hz
  have hzpos : 0 < z.re := by
    rw [hz, centered_re_v13]
    linarith
  have ha' : WeilZeroCoefficientV11 g rho0 ≠ 0 := ha
  classical
  let a : RiemannNontrivialZeroIndexV2 → ℂ := WeilZeroCoefficientV11 g
  let b : RiemannNontrivialZeroIndexV2 → ℂ := fun rho => if rho = rho0 then 0 else a rho
  have hb : Summable (fun rho => ‖b rho‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun rho => ?_)
      (zero_coefficient_norm_summable_v12 g)
    by_cases hr : rho = rho0
    · simp [b, hr]
    · simp only [b, hr, if_false]
      exact le_rfl
  obtain ⟨ε₁, hε₁, hiso⟩ := exists_sep_of_centered_zero_v13 rho0
  have hH : AnalyticAt ℂ (ResolventSumV13 b) z := by
    refine resolventSum_analyticAt_v13 b hb z hε₁ (fun rho hb0 => ?_)
    have hne : rho ≠ rho0 := by
      intro heq
      apply hb0
      simp [b, heq]
    exact hiso rho hne
  have hLc : ContinuousAt (WeilZeroKernelLaplaceV12 g) z :=
    (zero_kernel_laplace_analyticOnNhd_of_bound g C hK z hzpos).continuousAt
  -- pointwise split of the resolvent on the bridge domain
  have hsplit : ∀ w ∈ BridgeDomainV13,
      WeilZeroResolventV12 g w = a rho0 / (w - z) + ResolventSumV13 b w := by
    intro w hw
    obtain ⟨ε, hε, hsep⟩ :=
      exists_sep_of_not_centered_zero_v13 w hw.1 (fun rho heq => hw.2 ⟨rho, heq⟩)
    have hs : Summable (fun rho => a rho / (w - WeilCenteredZeroExponentV12 rho)) := by
      refine Summable.of_norm_bounded
        ((zero_coefficient_norm_summable_v12 g).mul_left (1 / ε)) (fun rho => ?_)
      rw [norm_div]
      have hl := hsep rho
      have hpos : 0 < ‖w - WeilCenteredZeroExponentV12 rho‖ := lt_of_lt_of_le hε hl
      rw [div_le_iff₀ hpos]
      calc
        ‖a rho‖ = (1 / ε * ‖a rho‖) * ε := by field_simp
        _ ≤ (1 / ε * ‖a rho‖) * ‖w - WeilCenteredZeroExponentV12 rho‖ := by
          gcongr
    unfold WeilZeroResolventV12 ResolventSumV13
    rw [hs.tsum_eq_add_tsum_ite rho0]
    congr 1
    apply tsum_congr
    intro rho
    by_cases hr : rho = rho0
    · simp [b, hr]
    · simp only [b, hr, if_false]
  -- punctured neighbourhood of z inside the bridge domain
  let δ : ℝ := min ε₁ z.re
  have hδ : 0 < δ := lt_min hε₁ hzpos
  have hnear : ∀ w ∈ Metric.ball z δ, w ≠ z → w ∈ BridgeDomainV13 := by
    intro w hw hne
    have hd : ‖w - z‖ < δ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    refine ⟨?_, ?_⟩
    · show 0 < w.re
      have hreabs : |w.re - z.re| ≤ ‖w - z‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - z)
      have hlo := (abs_lt.mp (lt_of_le_of_lt hreabs hd)).1
      have hmin : δ ≤ z.re := min_le_right _ _
      linarith
    · rintro ⟨rho, hrho⟩
      have hrho' : WeilCenteredZeroExponentV12 rho = w := hrho
      have hne' : rho ≠ rho0 := by
        intro heq
        apply hne
        rw [← hrho', heq]
      have h1 := hiso rho hne'
      have hmin : δ ≤ ε₁ := min_le_left _ _
      rw [hrho', norm_sub_rev, ← hz] at h1
      linarith
  have heq : WeilZeroKernelLaplaceV12 g =ᶠ[𝓝[≠] z]
      fun w => a rho0 / (w - z) + ResolventSumV13 b w := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hδ),
      self_mem_nhdsWithin] with w hw hne
    have hwz : w ≠ z := by simpa using hne
    have hwD := hnear w hw hwz
    rw [laplace_eq_resolvent_on_domain_of_bound g C hK hwD, hsplit w hwD]
  exact continuous_cannot_equal_nonzero_simple_pole_v13 hLc hH.continuousAt ha' heq

/-- A bounded packet kernel rules out every right-hand zero it detects. -/
theorem zero_re_le_half_of_detecting_bounded_kernel (g : WeilCompactSmoothGV1)
    (rho0 : RiemannNontrivialZeroIndexV2) (ha : WeilZeroCoefficientV11 g rho0 ≠ 0)
    (hK : PacketKernelBoundV1 g) : rho0.1.re ≤ 1 / 2 := by
  obtain ⟨C, hC⟩ := hK
  exact zero_re_le_half_of_detecting_kernel_bound g C hC rho0 ha

/-- One detecting packet with a bounded translated zero kernel proves Mathlib RH. -/
theorem riemannHypothesis_of_detecting_bounded_kernel (g : WeilCompactSmoothGV1)
    (hdetect : ∀ rho : RiemannNontrivialZeroIndexV2, WeilZeroCoefficientV11 g rho ≠ 0)
    (hK : PacketKernelBoundV1 g) : RiemannHypothesis := by
  intro s hz hnt _
  let rho : RiemannNontrivialZeroIndexV2 := ⟨s, hz, hnt⟩
  have h1 : s.re ≤ 1 / 2 :=
    zero_re_le_half_of_detecting_bounded_kernel g rho (hdetect rho) hK
  obtain ⟨sigma, hsig⟩ := exists_reflected_zero_v13 rho
  have h2 := zero_re_le_half_of_detecting_bounded_kernel g sigma (hdetect sigma) hK
  rw [hsig] at h2
  simp at h2
  linarith

#print axioms AEGIS.RHDetectingPacketCriterionV1.zero_kernel_laplace_analyticOnNhd_of_bound
#print axioms AEGIS.RHDetectingPacketCriterionV1.zero_re_le_half_of_detecting_bounded_kernel
#print axioms AEGIS.RHDetectingPacketCriterionV1.riemannHypothesis_of_detecting_bounded_kernel

end AEGIS.RHDetectingPacketCriterionV1
