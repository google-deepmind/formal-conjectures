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

import RHFixedPacketFrontierV1

/-!
# Subexponential growth criterion for the fixed RH detector

The bounded-kernel criterion is stronger than necessary.  The Laplace/pole
argument only needs the translated zero kernel to have exponential type zero on
the positive half-line.

We use the concrete majorant formulation

  forall epsilon > 0, exists C >= 0, forall t >= 0,
    ||K(t)|| <= C * exp(epsilon * t).

For a Laplace parameter w with Re(w)>0 choose epsilon = Re(w)/2.  The
weighted kernel is then dominated by an integrable exponential tail.  The same
choice with a smaller local epsilon dominates the w-derivative.  Hence the
Laplace transform is analytic on the entire open right half-plane, and the
existing resolvent/nonremovable-pole argument applies unchanged.

This file does NOT prove the subexponential estimate.  It only replaces the
older uniform-boundedness input by the strictly weaker growth-zero input.

A useful next arithmetic target is a dyadic self-compression estimate.  If for
some fixed C and all sufficiently large d one can prove

  1 + |S(2*d)| <= C * (1 + |S(d)|),

then iteration gives at most polynomial growth in d, hence the
subexponential premise below.  No such doubling estimate is asserted here.

AUTHORITY_EFFECT = NONE.
RH_PROVEN_UNCONDITIONALLY = false.
-/

open Set Filter Topology Complex MeasureTheory
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKernelSubexponentialV1

open AEGIS.WeilZeroTwoPointV11
open AEGIS.RHZeroKernelLaplaceV12
open AEGIS.RHZeroKernelLaplaceAnalyticV12
open AEGIS.RHRestrictedWeilBridgeV13
open AEGIS.RestrictedWeilCriterionFinalV13
open AEGIS.RHDetectingPacketCriterionV1
open AEGIS.RHFixedPacketFrontierV1
open AEGIS.RHFixedPacketFourPhaseV1
open AEGIS.WeilRHImpliesFinalSignV13

/-- Exponential type zero on the positive half-line, in a form directly useful
for Laplace domination. -/
def PacketKernelSubexponentialV1 (g : WeilCompactSmoothGV1) : Prop :=
  forall epsilon : Real, 0 < epsilon ->
    exists C : Real, 0 <= C ∧ forall t : Real, 0 <= t ->
      norm (WeilZeroTranslationKernelV11 g t) <=
        C * Real.exp (epsilon * t)

/-- The old uniform bound implies the new subexponential interface. -/
theorem packetKernelSubexponential_of_bound
    (g : WeilCompactSmoothGV1) (hK : PacketKernelBoundV1 g) :
    PacketKernelSubexponentialV1 g := by
  obtain ⟨C, hC⟩ := hK
  have hC0 : 0 <= C :=
    (norm_nonneg (WeilZeroTranslationKernelV11 g 0)).trans (hC 0)
  intro epsilon hepsilon
  refine ⟨C, hC0, ?_⟩
  intro t ht
  have hexp : 1 <= Real.exp (epsilon * t) := by
    exact Real.one_le_exp (mul_nonneg hepsilon.le ht)
  calc
    norm (WeilZeroTranslationKernelV11 g t) <= C := hC t
    _ = C * 1 := by ring
    _ <= C * Real.exp (epsilon * t) :=
      mul_le_mul_of_nonneg_left hexp hC0

/-- A subexponential kernel has an integrable Laplace transform at every
parameter with positive real part. -/
theorem zero_kernel_laplace_integrable_of_subexponential
    (g : WeilCompactSmoothGV1) (hK : PacketKernelSubexponentialV1 g)
    (w : Complex) (hw : 0 < w.re) :
    IntegrableOn
      (fun t : Real =>
        Complex.exp (-(w * (t : Complex))) *
          WeilZeroTranslationKernelV11 g t)
      (Ioi (0 : Real)) := by
  let delta : Real := w.re / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  obtain ⟨C, hC0, hC⟩ := hK delta hdelta
  have hmajor :
      IntegrableOn
        (fun t : Real => C * Real.exp (-(delta * t)))
        (Ioi (0 : Real)) := by
    change Integrable
      (fun t : Real => C * Real.exp (-(delta * t)))
      (volume.restrict (Ioi (0 : Real)))
    simpa [neg_mul] using
      (integrableOn_exp_mul_Ioi (a := -delta) (by linarith) 0).const_mul C
  have hmeas :
      AEStronglyMeasurable
        (fun t : Real =>
          Complex.exp (-(w * (t : Complex))) *
            WeilZeroTranslationKernelV11 g t)
        (volume.restrict (Ioi (0 : Real))) := by
    exact
      ((by fun_prop :
        Continuous (fun t : Real =>
          Complex.exp (-(w * (t : Complex))))).aestronglyMeasurable.mul
        (zero_translation_kernel_continuous_v12 g).aestronglyMeasurable).restrict
  refine hmajor.mono' hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact Filter.Eventually.of_forall (fun t ht => by
    have ht0 : 0 <= t := le_of_lt ht
    rw [norm_mul, Complex.norm_exp]
    have hk := hC t ht0
    have hre :
        (-(w * (t : Complex))).re = -w.re * t := by
      simp
    rw [hre]
    calc
      Real.exp (-w.re * t) * norm (WeilZeroTranslationKernelV11 g t)
          <= Real.exp (-w.re * t) *
              (C * Real.exp (delta * t)) :=
        mul_le_mul_of_nonneg_left hk (Real.exp_nonneg _)
      _ = C * (Real.exp (-w.re * t) * Real.exp (delta * t)) := by ring
      _ = C * Real.exp ((-w.re * t) + delta * t) := by
        rw [Real.exp_add]
      _ = C * Real.exp (-(delta * t)) := by
        congr 2
        dsimp [delta]
        ring)

/-- First-moment exponential tail used for local differentiation under the
integral sign. -/
private theorem first_moment_exp_tail_integrable_subexp
    (delta C : Real) (hdelta : 0 < delta) :
    IntegrableOn
      (fun t : Real => C * (t * Real.exp (-(delta * t))))
      (Ioi (0 : Real)) := by
  by_cases hC : C = 0
  · simp [hC]
  have hbase :
      IntegrableOn
        (fun t : Real => t * Real.exp (-(delta * t)))
        (Ioi (0 : Real)) := by
    have hI :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := delta)
        (by norm_num) (by norm_num) hdelta
    refine hI.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [Real.rpow_one]
  exact hbase.const_mul C

/-- Differentiability of the subexponential-kernel Laplace transform at every
point of the open right half-plane. -/
theorem zero_kernel_laplace_differentiableAt_of_subexponential
    (g : WeilCompactSmoothGV1) (hK : PacketKernelSubexponentialV1 g)
    (w0 : Complex) (hw0 : 0 < w0.re) :
    DifferentiableAt Complex (WeilZeroKernelLaplaceV12 g) w0 := by
  let r : Real := w0.re / 4
  have hr : 0 < r := by
    dsimp [r]
    linarith
  obtain ⟨C, hC0, hC⟩ := hK r hr

  let F : Complex -> Real -> Complex := fun w t =>
    Complex.exp (-(w * (t : Complex))) *
      WeilZeroTranslationKernelV11 g t
  let F' : Complex -> Real -> Complex := fun w t =>
    (-(t : Complex)) *
      Complex.exp (-(w * (t : Complex))) *
        WeilZeroTranslationKernelV11 g t
  let bound : Real -> Real := fun t =>
    C * (t * Real.exp (-(r * t)))

  have hs : Metric.ball w0 r ∈ nhds w0 :=
    Metric.ball_mem_nhds _ hr

  have hFmeas :
      ∀ᶠ w in nhds w0,
        AEStronglyMeasurable (F w)
          (volume.restrict (Ioi (0 : Real))) := by
    exact Filter.Eventually.of_forall (fun w => by
      apply AEStronglyMeasurable.restrict
      exact
        ((by fun_prop :
          Continuous (fun t : Real =>
            Complex.exp (-(w * (t : Complex))))).aestronglyMeasurable.mul
          (zero_translation_kernel_continuous_v12 g).aestronglyMeasurable))

  have hFint :
      Integrable (F w0) (volume.restrict (Ioi (0 : Real))) := by
    exact zero_kernel_laplace_integrable_of_subexponential
      g hK w0 hw0

  have hF'meas :
      AEStronglyMeasurable (F' w0)
        (volume.restrict (Ioi (0 : Real))) := by
    apply AEStronglyMeasurable.restrict
    exact
      ((by fun_prop :
        Continuous (fun t : Real =>
          (-(t : Complex)) *
            Complex.exp (-(w0 * (t : Complex))))).aestronglyMeasurable.mul
        (zero_translation_kernel_continuous_v12 g).aestronglyMeasurable)

  have hbound :
      ∀ᵐ t ∂(volume.restrict (Ioi (0 : Real))),
        ∀ w ∈ Metric.ball w0 r, norm (F' w t) <= bound t := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun t ht w hw => by
      have ht0 : 0 <= t := le_of_lt ht
      have hdist : norm (w - w0) < r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hw
      have hreDiff : abs (w.re - w0.re) <= norm (w - w0) := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - w0)
      have hlo := (abs_lt.mp (lt_of_le_of_lt hreDiff hdist)).1
      have hwre : 2 * r <= w.re := by
        dsimp only [r] at hlo ⊢
        linarith
      have hk := hC t ht0
      simp only [F', bound]
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ht0, Complex.norm_exp]
      have hre :
          (-(w * (t : Complex))).re = -w.re * t := by
        simp
      rw [hre]
      calc
        t * Real.exp (-w.re * t) *
            norm (WeilZeroTranslationKernelV11 g t)
          <= t * Real.exp (-w.re * t) *
              (C * Real.exp (r * t)) := by
                gcongr
        _ = C * (t * Real.exp ((-w.re * t) + r * t)) := by
              rw [Real.exp_add]
              ring
        _ <= C * (t * Real.exp (-(r * t))) := by
              gcongr
              have hmul : 0 <= (w.re - 2 * r) * t :=
                mul_nonneg (sub_nonneg.mpr hwre) ht0
              nlinarith)

  have hboundInt :
      Integrable bound (volume.restrict (Ioi (0 : Real))) := by
    exact first_moment_exp_tail_integrable_subexp r C hr

  have hdiff :
      ∀ᵐ t ∂(volume.restrict (Ioi (0 : Real))),
        ∀ w ∈ Metric.ball w0 r,
          HasDerivAt (F · t) (F' w t) w := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun t ht w hw => by
      simp only [F, F']
      have hinner :
          HasDerivAt (fun z : Complex => -(z * (t : Complex))) (-(t : Complex)) w :=
        (hasDerivAt_mul_const (t : Complex)).neg
      have hExp :
          HasDerivAt
            (fun z : Complex => Complex.exp (-(z * (t : Complex))))
            (-(t : Complex) *
              Complex.exp (-(w * (t : Complex)))) w :=
        hinner.cexp.congr_deriv (by ring)
      exact hExp.mul_const
        (WeilZeroTranslationKernelV11 g t))

  have main :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (0 : Real)))
      (F := F) (F' := F') (bound := bound)
      hs hFmeas hFint hF'meas hbound hboundInt hdiff

  exact main.2.differentiableAt

/-- A subexponential translated kernel has a holomorphic Laplace transform on
the whole open right half-plane. -/
theorem zero_kernel_laplace_analyticOnNhd_of_subexponential
    (g : WeilCompactSmoothGV1) (hK : PacketKernelSubexponentialV1 g) :
    AnalyticOnNhd Complex
      (WeilZeroKernelLaplaceV12 g)
      ZeroLaplaceRightHalfPlaneV12 := by
  apply DifferentiableOn.analyticOnNhd
  · intro w hw
    exact
      (zero_kernel_laplace_differentiableAt_of_subexponential
        g hK w hw).differentiableWithinAt
  · exact zeroLaplaceRightHalfPlane_isOpen_v12

theorem laplace_eq_resolvent_on_domain_of_subexponential
    (g : WeilCompactSmoothGV1) (hK : PacketKernelSubexponentialV1 g) :
    EqOn (WeilZeroKernelLaplaceV12 g) (WeilZeroResolventV12 g) BridgeDomainV13 := by
  have hL : AnalyticOnNhd Complex (WeilZeroKernelLaplaceV12 g) BridgeDomainV13 :=
    (zero_kernel_laplace_analyticOnNhd_of_subexponential g hK).mono (fun w hw => hw.1)
  have hR : AnalyticOnNhd Complex (WeilZeroResolventV12 g) BridgeDomainV13 := by
    intro w hw
    obtain ⟨epsilon, hepsilon, hsep⟩ :=
      exists_sep_of_not_centered_zero_v13 w hw.1 (fun rho heq => hw.2 ⟨rho, heq⟩)
    rw [resolvent_eq_resolventSum_v13]
    exact resolventSum_analyticAt_v13 (WeilZeroCoefficientV11 g)
      (zero_coefficient_norm_summable_v12 g) w hepsilon (fun rho _ => hsep rho)
  refine hL.eqOn_of_preconnected_of_eventuallyEq hR bridgeDomain_isPreconnected_v13
    one_mem_bridgeDomain_v13 ?_
  have hopen : IsOpen {w : Complex | (1 / 2 : Real) < w.re} :=
    Complex.continuous_re.isOpen_preimage (Ioi (1 / 2 : Real)) isOpen_Ioi
  have hmem : {w : Complex | (1 / 2 : Real) < w.re} ∈ nhds (1 : Complex) :=
    hopen.mem_nhds (by simp; norm_num)
  filter_upwards [hmem] with w hw
  exact zero_kernel_laplace_eq_resolvent_v12 g w hw

/-- A subexponential packet kernel rules out every right-hand zero that the
packet detects. -/
theorem zero_re_le_half_of_detecting_subexponential_kernel
    (g : WeilCompactSmoothGV1)
    (hK : PacketKernelSubexponentialV1 g)
    (rho0 : RiemannNontrivialZeroIndexV2)
    (ha : WeilZeroCoefficientV11 g rho0 ≠ 0) :
    rho0.1.re <= 1 / 2 := by
  by_contra hlt
  have hlt' : 1 / 2 < rho0.1.re := lt_of_not_ge hlt
  set z : Complex := WeilCenteredZeroExponentV12 rho0 with hz
  have hzpos : 0 < z.re := by
    rw [hz, centered_re_v13]
    linarith
  have ha' : WeilZeroCoefficientV11 g rho0 ≠ 0 := ha
  classical
  let a : RiemannNontrivialZeroIndexV2 -> Complex := WeilZeroCoefficientV11 g
  let b : RiemannNontrivialZeroIndexV2 -> Complex := fun rho => if rho = rho0 then 0 else a rho
  have hb : Summable (fun rho => norm (b rho)) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun rho => ?_)
      (zero_coefficient_norm_summable_v12 g)
    by_cases hr : rho = rho0
    · simp [b, hr]
    · simp only [b, hr, if_false]
      exact le_rfl
  obtain ⟨epsilon1, hepsilon1, hiso⟩ := exists_sep_of_centered_zero_v13 rho0
  have hH : AnalyticAt Complex (ResolventSumV13 b) z := by
    refine resolventSum_analyticAt_v13 b hb z hepsilon1 (fun rho hb0 => ?_)
    have hne : rho ≠ rho0 := by
      intro heq
      apply hb0
      simp [b, heq]
    exact hiso rho hne
  have hLc : ContinuousAt (WeilZeroKernelLaplaceV12 g) z :=
    (zero_kernel_laplace_analyticOnNhd_of_subexponential g hK z hzpos).continuousAt
  have hsplit : ∀ w ∈ BridgeDomainV13,
      WeilZeroResolventV12 g w = a rho0 / (w - z) + ResolventSumV13 b w := by
    intro w hw
    obtain ⟨epsilon, hepsilon, hsep⟩ :=
      exists_sep_of_not_centered_zero_v13 w hw.1 (fun rho heq => hw.2 ⟨rho, heq⟩)
    have hs : Summable (fun rho => a rho / (w - WeilCenteredZeroExponentV12 rho)) := by
      refine Summable.of_norm_bounded
        ((zero_coefficient_norm_summable_v12 g).mul_left (1 / epsilon)) (fun rho => ?_)
      rw [norm_div]
      have hl := hsep rho
      have hpos : 0 < norm (w - WeilCenteredZeroExponentV12 rho) := lt_of_lt_of_le hepsilon hl
      rw [div_le_iff₀ hpos]
      calc
        norm (a rho) = (1 / epsilon * norm (a rho)) * epsilon := by field_simp
        _ <= (1 / epsilon * norm (a rho)) *
              norm (w - WeilCenteredZeroExponentV12 rho) := by
          gcongr
    unfold WeilZeroResolventV12 ResolventSumV13
    rw [hs.tsum_eq_add_tsum_ite rho0]
    congr 1
    apply tsum_congr
    intro rho
    by_cases hr : rho = rho0
    · simp [b, hr]
    · simp only [b, hr, if_false]
  let delta : Real := min epsilon1 z.re
  have hdelta : 0 < delta := lt_min hepsilon1 hzpos
  have hnear : ∀ w ∈ Metric.ball z delta, w ≠ z -> w ∈ BridgeDomainV13 := by
    intro w hw hne
    have hd : norm (w - z) < delta := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    refine ⟨?_, ?_⟩
    · show 0 < w.re
      have hreabs : abs (w.re - z.re) <= norm (w - z) := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - z)
      have hlo := (abs_lt.mp (lt_of_le_of_lt hreabs hd)).1
      have hmin : delta <= z.re := min_le_right _ _
      linarith
    · rintro ⟨rho, hrho⟩
      have hrho' : WeilCenteredZeroExponentV12 rho = w := hrho
      have hne' : rho ≠ rho0 := by
        intro heq
        apply hne
        rw [← hrho', heq]
      have h1 := hiso rho hne'
      have hmin : delta <= epsilon1 := min_le_left _ _
      rw [hrho', norm_sub_rev, ← hz] at h1
      linarith
  have heq : WeilZeroKernelLaplaceV12 g =ᶠ[nhdsWithin z {z}ᶜ]
      fun w => a rho0 / (w - z) + ResolventSumV13 b w := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hdelta),
      self_mem_nhdsWithin] with w hw hne
    have hwz : w ≠ z := by simpa using hne
    have hwD := hnear w hw hwz
    rw [laplace_eq_resolvent_on_domain_of_subexponential g hK hwD, hsplit w hwD]
  exact continuous_cannot_equal_nonzero_simple_pole_v13 hLc hH.continuousAt ha' heq

/-- One detecting packet with subexponential translated-kernel growth proves
Mathlib's Riemann hypothesis. -/
theorem riemannHypothesis_of_detecting_subexponential_kernel
    (g : WeilCompactSmoothGV1)
    (hdetect : forall rho : RiemannNontrivialZeroIndexV2,
      WeilZeroCoefficientV11 g rho ≠ 0)
    (hK : PacketKernelSubexponentialV1 g) :
    RiemannHypothesis := by
  intro s hz hnt _
  let rho : RiemannNontrivialZeroIndexV2 := ⟨s, hz, hnt⟩
  have h1 : s.re <= 1 / 2 :=
    zero_re_le_half_of_detecting_subexponential_kernel g hK rho (hdetect rho)
  obtain ⟨sigma, hsig⟩ := exists_reflected_zero_v13 rho
  have h2 :=
    zero_re_le_half_of_detecting_subexponential_kernel g hK sigma (hdetect sigma)
  rw [hsig] at h2
  simp at h2
  linarith

/-- Subexponential growth of the repository's one fixed detecting packet is
already sufficient for RH. -/
theorem riemannHypothesis_of_fixed_detecting_packet_subexponential
    (hK : PacketKernelSubexponentialV1 detectingPacket) :
    RiemannHypothesis :=
  riemannHypothesis_of_detecting_subexponential_kernel detectingPacket
    detectingPacket_detects hK

/-- For the fixed detector, exponential type zero is exactly equivalent to RH.
The reverse direction reuses the already-proved RH -> universal sign -> fixed
four-phase sign -> bounded kernel chain. -/
theorem fixed_detecting_packet_subexponential_iff_rh :
    PacketKernelSubexponentialV1 detectingPacket <-> RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_fixed_detecting_packet_subexponential
  · intro hRH
    apply packetKernelSubexponential_of_bound
    exact fixed_packet_four_phase_implies_bounded_zero_kernel detectingPacket
      detectingPacket_moments
      ((fixed_detecting_packet_sign_iff_universal).2
        (rh_implies_universal_v13 hRH))

#print axioms AEGIS.RHKernelSubexponentialV1.zero_kernel_laplace_analyticOnNhd_of_subexponential
#print axioms AEGIS.RHKernelSubexponentialV1.zero_re_le_half_of_detecting_subexponential_kernel
#print axioms AEGIS.RHKernelSubexponentialV1.riemannHypothesis_of_fixed_detecting_packet_subexponential
#print axioms AEGIS.RHKernelSubexponentialV1.fixed_detecting_packet_subexponential_iff_rh

end AEGIS.RHKernelSubexponentialV1
