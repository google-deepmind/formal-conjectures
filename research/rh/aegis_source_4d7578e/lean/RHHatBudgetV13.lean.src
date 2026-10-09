import RHThreeCellGainV13
import RHHatKernelV13
import RHThresholdClassV13
import WeilAutocorrelationClosureV1

/-!
AEGIS Ω — the Weil diagonal with a positive-definite hat kernel, V13.

Write `c(u) = Re C(u)` for the logarithmic autocorrelation, `E` for the energy and
`K = hatK h n v` for a hat kernel.  Three facts are combined on `(0, 2r]`:

* the moment identity `∫ 2cosh(u/2)·c = 0` (multiplier `λ`),
* positive definiteness `∫ c·K ≥ 0` (`RHHatPosDefV13`, multiplier `σ ≥ 0`),
* the caps `c ≤ E`, `c ≤ 0.71E` for `3u > 2r`, `c ≤ E/2` for `u > r`.

If `Q(u) = e^{u/2}/sinh u − 2λ cosh(u/2) + σK(u) ≥ 0` on `(0, 2r]`, the integrand
`(e^{u/2}c − E)/sinh u − λ·2cosh(u/2)c + σcK` is at most
`−(1−cap)E/sinh u + cap·E·(1/2 + u/8 − 2λcosh(u/2) + σK(u))`, and integrating gives
`hatBudget`.  Unlike pointwise caps, the kernel `K` uses the positive-definite structure
of `c`, which is what the Weil form needs beyond support ≈ 0.48.
Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHHatBudgetV13
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilWidthArchBudgetV26
open AEGIS.WeilWidthArchIntegralV27
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHMomentPiecesV13
open AEGIS.RHMomentGainV13
open AEGIS.RHMomentIdentityV13
open AEGIS.RHHalfCapV13
open AEGIS.RHThreeCellV13
open AEGIS.RHThresholdClassV13
open AEGIS.RHHatPosDefV13
open AEGIS.RHHatKernelV13

/-- The logarithmic lift is continuous (as in `WeilWidthArchCorrelationV25`). -/
theorem logLift_continuous (g : WeilCompactSmoothGV1) : Continuous (logLift g.1) := by
  unfold logLift
  have hscalar : Continuous (fun t : ℝ => (Real.exp (t / 2) : ℂ)) := by fun_prop
  exact hscalar.mul (g.2.1.continuous.comp Real.continuous_exp)

/-- The logarithmic lift has compact support (as in `WeilWidthArchCorrelationV25`). -/
theorem logLift_hasCompactSupport (g : WeilCompactSmoothGV1) :
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

/-- Real part of the logarithmic autocorrelation. -/
def cRe (g : WeilCompactSmoothGV1) (u : ℝ) : ℝ := (logCorrelationV25 g u).re

theorem cRe_eq (g : WeilCompactSmoothGV1) (u : ℝ) :
    Real.exp u * (WeilAutocorrelationV1 g (Real.exp u)).re = Real.exp (u / 2) * cRe g u := by
  unfold cRe
  rw [logCorrelation_eq_autocorrelation_v25, Complex.re_ofReal_mul, ← mul_assoc,
    ← Real.exp_add]
  congr 2; ring

theorem logCorrelation_continuous (g : WeilCompactSmoothGV1) :
    Continuous (logCorrelationV25 g) := by
  have e : logCorrelationV25 g = fun u =>
      (Real.exp (u / 2) : ℂ) * WeilAutocorrelationV1 g (Real.exp u) := by
    funext u; exact logCorrelation_eq_autocorrelation_v25 g u
  rw [e]
  have hA : Continuous (WeilAutocorrelationV1 g) :=
    (WeilAutocorrelationCompactSmoothV1 g).2.1.continuous
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))).mul
    (hA.comp Real.continuous_exp)

theorem cRe_continuous (g : WeilCompactSmoothGV1) : Continuous (cRe g) :=
  Complex.continuous_re.comp (logCorrelation_continuous g)

theorem cRe_zero (g : WeilCompactSmoothGV1) (r a u : ℝ) (hw : HalfWidthAt g r a)
    (hu : 2 * r < u) : cRe g u = 0 := by
  unfold cRe
  rw [logCorrelation_eq_autocorrelation_v25, autocorrelation_zero_of_halfWidth g r a u hw hu]
  simp

/-- Positive definiteness for the packet's own autocorrelation. -/
theorem hat_posdef_packet (g : WeilCompactSmoothGV1) (h : ℝ) (hh : 0 ≤ h) (n : ℕ)
    (v : ℕ → ℝ) : 0 ≤ ∫ u in Ioi (0 : ℝ), cRe g u * hatK h n v u := by
  have hC : Continuous (corrC (logLift g.1)) := logCorrelation_continuous g
  exact hat_posdef_Ioi (logLift g.1) (logLift_continuous g) (logLift_hasCompactSupport g)
    h hh hC n v

/-- `(e^{u/2} − 1)/sinh u ≤ 1/2 + u/8` on `(0, 1]`. -/
theorem w_upper (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    (Real.exp (u / 2) - 1) / Real.sinh u ≤ 1 / 2 + u / 8 := by
  obtain ⟨-, he⟩ := exp_pos_enc (u / 2) (by linarith) (by linarith)
  obtain ⟨hp, -⟩ := exp_pos_enc u hu0 hu1
  obtain ⟨-, hn⟩ := exp_neg_enc u hu0 hu1
  have hs : u + u ^ 3 / 6 - u ^ 5 / 100 ≤ Real.sinh u := by
    rw [Real.sinh_eq]; linarith
  have hs0 : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  rw [div_le_iff₀ hs0]
  have h3 : 0 < u ^ 3 := by positivity
  have hpoly : (u / 2) + (u / 2) ^ 2 / 2 + (u / 2) ^ 3 / 6 + (u / 2) ^ 4 / 24 + (u / 2) ^ 5 / 100 ≤
      (1 / 2 + u / 8) * (u + u ^ 3 / 6 - u ^ 5 / 100) := by
    have hu2 : u ^ 2 ≤ 1 := by nlinarith
    have hu3 : u ^ 3 ≤ 1 := by nlinarith
    nlinarith [mul_pos h3 hu0, mul_nonneg h3.le (sq_nonneg u)]
  nlinarith [mul_le_mul_of_nonneg_left hs (by linarith : (0 : ℝ) ≤ 1 / 2 + u / 8)]

/-- The combined integrand. -/
def hatIntegrand (g : WeilCompactSmoothGV1) (lam σ h : ℝ) (n : ℕ) (v : ℕ → ℝ) (u : ℝ) : ℝ :=
  widthArchLogIntegrandV26 g u - lam * momentLog g u + σ * (cRe g u * hatK h n v u)

/-- The kernel condition. -/
def kernelQ (lam σ h : ℝ) (n : ℕ) (v : ℕ → ℝ) (u : ℝ) : ℝ :=
  Real.exp (u / 2) / Real.sinh u - 2 * lam * Real.cosh (u / 2) + σ * hatK h n v u

theorem hatIntegrand_form (g : WeilCompactSmoothGV1) (lam σ h : ℝ) (n : ℕ) (v : ℕ → ℝ)
    (u : ℝ) :
    hatIntegrand g lam σ h n v u =
      -energy g.1 / Real.sinh u + cRe g u * kernelQ lam σ h n v u := by
  unfold hatIntegrand widthArchLogIntegrandV26 momentLog kernelQ
  rw [cRe_eq]
  have hm : Real.exp (u / 2) * cRe g u * (1 + Real.exp (-u)) =
      cRe g u * (2 * Real.cosh (u / 2)) := by
    rw [mul_comm (Real.exp (u / 2)), mul_assoc, exp_half_mul]
  rw [show Real.exp (u / 2) * cRe g u * (1 + Real.exp (-u)) =
    cRe g u * (2 * Real.cosh (u / 2)) from hm]
  ring

/-- Pointwise majorant with a cap. -/
theorem hatIntegrand_le (g : WeilCompactSmoothGV1) (lam σ h : ℝ) (n : ℕ) (v : ℕ → ℝ)
    (u cap : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (hcap0 : 0 ≤ cap)
    (hQ : 0 ≤ kernelQ lam σ h n v u) (hc : cRe g u ≤ cap * energy g.1) :
    hatIntegrand g lam σ h n v u ≤
      -(1 - cap) * energy g.1 * (1 / Real.sinh u) +
        cap * energy g.1 * (1 / 2 + u / 8 - 2 * lam * Real.cosh (u / 2) +
          σ * hatK h n v u) := by
  have hE := energy_nonnegative g.1
  have hs0 : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  rw [hatIntegrand_form]
  have h1 : cRe g u * kernelQ lam σ h n v u ≤ cap * energy g.1 * kernelQ lam σ h n v u :=
    mul_le_mul_of_nonneg_right hc hQ
  have hw := w_upper u hu0 hu1
  have hQe : kernelQ lam σ h n v u = (Real.exp (u / 2) - 1) / Real.sinh u + 1 / Real.sinh u -
      2 * lam * Real.cosh (u / 2) + σ * hatK h n v u := by
    unfold kernelQ; field_simp; ring
  have hcE : 0 ≤ cap * energy g.1 := mul_nonneg hcap0 hE
  have h2 := mul_le_mul_of_nonneg_left hw hcE
  rw [hQe] at h1
  have e : -energy g.1 / Real.sinh u = -energy g.1 * (1 / Real.sinh u) := by ring
  rw [e]
  nlinarith

theorem hatIntegrand_integrableOn (g : WeilCompactSmoothGV1) (lam σ h : ℝ) (n : ℕ)
    (v : ℕ → ℝ) (a b : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (hatIntegrand g lam σ h n v) (Ioc a b) := by
  have hsub : Ioc a b ⊆ Ioi (0 : ℝ) := fun u hu => lt_of_le_of_lt ha hu.1
  have h1 := (width_arch_log_integrableOn_v27 g).mono_set hsub
  have h2 := ((moment_log_integrableOn g).mono_set hsub).const_mul lam
  have h3 : IntegrableOn (fun u => σ * (cRe g u * hatK h n v u)) (Ioc a b) :=
    ((continuous_const.mul ((cRe_continuous g).mul (hatK_continuous h n v))).integrableOn_Ioc)
  exact (h1.sub h2).add h3

theorem poly_integral (a b : ℝ) (hab : a ≤ b) :
    ∫ u in Ioc a b, (1 / 2 + u / 8) = (b - a) / 2 + (b ^ 2 - a ^ 2) / 16 := by
  rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_add
    (f := fun _ => (1 / 2 : ℝ)) (g := fun u => u / 8) intervalIntegrable_const
    ((continuous_id.div_const 8).intervalIntegrable _ _), intervalIntegral.integral_const,
    intervalIntegral.integral_div, integral_id]
  simp only [smul_eq_mul]
  ring

/-- The region integral of the majorant. -/
theorem region_integral (g : WeilCompactSmoothGV1) (lam σ h : ℝ) (n : ℕ) (v : ℕ → ℝ)
    (a b cap : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in Ioc a b, (-(1 - cap) * energy g.1 * (1 / Real.sinh u) +
        cap * energy g.1 * (1 / 2 + u / 8 - 2 * lam * Real.cosh (u / 2) +
          σ * hatK h n v u))) =
      -(1 - cap) * energy g.1 * (cothTail a - cothTail b) +
        cap * energy g.1 * ((b - a) / 2 + (b ^ 2 - a ^ 2) / 16 -
          4 * lam * (Real.sinh (b / 2) - Real.sinh (a / 2)) +
          σ * ∫ u in Ioc a b, hatK h n v u) := by
  have hs := integrableOn_inv_sinh_Ioc a b ha
  have hp : IntegrableOn (fun u : ℝ => 1 / 2 + u / 8) (Ioc a b) := by
    exact (continuous_const.add (continuous_id.div_const 8)).integrableOn_Ioc
  have hc := cosh_half_integrableOn a b
  have hk : IntegrableOn (hatK h n v) (Ioc a b) := (hatK_continuous h n v).integrableOn_Ioc
  have e : ∀ u, -(1 - cap) * energy g.1 * (1 / Real.sinh u) +
      cap * energy g.1 * (1 / 2 + u / 8 - 2 * lam * Real.cosh (u / 2) + σ * hatK h n v u) =
      (-(1 - cap) * energy g.1) * (1 / Real.sinh u) + (cap * energy g.1) * (1 / 2 + u / 8) -
        (cap * energy g.1 * 2 * lam) * Real.cosh (u / 2) +
        (cap * energy g.1 * σ) * hatK h n v u := by intro u; ring
  simp_rw [e]
  set E := energy g.1
  have h1 : IntegrableOn (fun u => (-(1 - cap) * E) * (1 / Real.sinh u)) (Ioc a b) :=
    hs.const_mul _
  have h2 : IntegrableOn (fun u : ℝ => (cap * E) * (1 / 2 + u / 8)) (Ioc a b) := hp.const_mul _
  have h3 : IntegrableOn (fun u => (cap * E * 2 * lam) * Real.cosh (u / 2)) (Ioc a b) :=
    hc.const_mul _
  have h4 : IntegrableOn (fun u => (cap * E * σ) * hatK h n v u) (Ioc a b) := hk.const_mul _
  have h12 : IntegrableOn (fun u => (-(1 - cap) * E) * (1 / Real.sinh u) +
      (cap * E) * (1 / 2 + u / 8)) (Ioc a b) := h1.add h2
  have h123 : IntegrableOn (fun u => (-(1 - cap) * E) * (1 / Real.sinh u) +
      (cap * E) * (1 / 2 + u / 8) - (cap * E * 2 * lam) * Real.cosh (u / 2)) (Ioc a b) :=
    h12.sub h3
  rw [integral_add h123 h4, integral_sub h12 h3, integral_add h1 h2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_inv_sinh_Ioc a b ha hab, poly_integral a b hab, integral_cosh_half a b hab]
  ring

theorem region_integral_zero (g : WeilCompactSmoothGV1) (lam σ h : ℝ) (n : ℕ) (v : ℕ → ℝ)
    (b : ℝ) (hb : 0 ≤ b) :
    (∫ u in Ioc 0 b, energy g.1 * (1 / 2 + u / 8 - 2 * lam * Real.cosh (u / 2) +
        σ * hatK h n v u)) =
      energy g.1 * (b / 2 + b ^ 2 / 16 - 4 * lam * Real.sinh (b / 2) +
        σ * ∫ u in Ioc 0 b, hatK h n v u) := by
  have hp : IntegrableOn (fun u : ℝ => 1 / 2 + u / 8) (Ioc 0 b) :=
    (continuous_const.add (continuous_id.div_const 8)).integrableOn_Ioc
  have hc := cosh_half_integrableOn 0 b
  have hk : IntegrableOn (hatK h n v) (Ioc 0 b) := (hatK_continuous h n v).integrableOn_Ioc
  have e : ∀ u, energy g.1 * (1 / 2 + u / 8 - 2 * lam * Real.cosh (u / 2) + σ * hatK h n v u) =
      energy g.1 * (1 / 2 + u / 8) - (energy g.1 * 2 * lam) * Real.cosh (u / 2) +
        (energy g.1 * σ) * hatK h n v u := by intro u; ring
  simp_rw [e]
  set E := energy g.1
  have h2 : IntegrableOn (fun u : ℝ => E * (1 / 2 + u / 8)) (Ioc 0 b) := hp.const_mul _
  have h3 : IntegrableOn (fun u => (E * 2 * lam) * Real.cosh (u / 2)) (Ioc 0 b) :=
    hc.const_mul _
  have h4 : IntegrableOn (fun u => (E * σ) * hatK h n v u) (Ioc 0 b) := hk.const_mul _
  have h23 : IntegrableOn (fun u : ℝ => E * (1 / 2 + u / 8) -
      (E * 2 * lam) * Real.cosh (u / 2)) (Ioc 0 b) := h2.sub h3
  rw [integral_add h23 h4, integral_sub h2 h3, integral_const_mul, integral_const_mul,
    integral_const_mul, poly_integral 0 b hb, integral_cosh_half 0 b hb]
  simp only [zero_div, Real.sinh_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow]
  ring

theorem cRe_le_energy (g : WeilCompactSmoothGV1) (u : ℝ) : cRe g u ≤ 1 * energy g.1 := by
  unfold cRe
  rw [one_mul]
  exact le_trans (Complex.re_le_norm _) (norm_logCorrelation_le_energy_v25 g u)

theorem hatIntegrand_le_one (g : WeilCompactSmoothGV1) (lam σ h : ℝ) (n : ℕ) (v : ℕ → ℝ)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (hQ : 0 ≤ kernelQ lam σ h n v u) :
    hatIntegrand g lam σ h n v u ≤
      energy g.1 * (1 / 2 + u / 8 - 2 * lam * Real.cosh (u / 2) + σ * hatK h n v u) := by
  have := hatIntegrand_le g lam σ h n v u 1 hu0 hu1 zero_le_one hQ (cRe_le_energy g u)
  simpa using this

theorem integral_zero_beyond (f : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b) (hf : IntegrableOn f (Ioi 0))
    (hz : ∀ u, b < u → f u = 0) :
    (∫ u in Ioi (0 : ℝ), f u) = ∫ u in Ioc 0 b, f u := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi hb, setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hf.mono_set (fun u hu => hu.1)) (hf.mono_set (fun u hu => lt_of_le_of_lt hb hu))]
  have : (∫ u in Ioi b, f u) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro u hu; exact hz u hu
  rw [this, add_zero]

/-- **Archimedean budget with a positive-definite hat kernel.** -/
theorem hat_arch_budget (g : WeilCompactSmoothGV1) (r a lam σ h t1 t2 : ℝ) (n : ℕ)
    (v : ℕ → ℝ) (hr0 : 0 < r) (hr1 : 2 * r ≤ 1) (hh : 0 ≤ h) (hσ : 0 ≤ σ)
    (ht1 : 0 < t1) (ht1' : 2 * r ≤ 3 * t1) (ht12 : t1 ≤ t2) (ht2 : r ≤ t2) (ht2' : t2 ≤ 2 * r)
    (hw : HalfWidthAt g r a) (hm : WeilMomentConditionsV1 g)
    (hQ : ∀ u ∈ Ioc 0 (2 * r), 0 ≤ kernelQ lam σ h n v u) :
    (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re ≤
      energy g.1 * (-cothTail (2 * r)
        + (t1 / 2 + t1 ^ 2 / 16 - 4 * lam * Real.sinh (t1 / 2) +
            σ * ∫ u in Ioc 0 t1, hatK h n v u)
        + (-(1 - 71 / 100) * (cothTail t1 - cothTail t2) +
            (71 / 100) * ((t2 - t1) / 2 + (t2 ^ 2 - t1 ^ 2) / 16 -
              4 * lam * (Real.sinh (t2 / 2) - Real.sinh (t1 / 2)) +
              σ * ∫ u in Ioc t1 t2, hatK h n v u))
        + (-(1 - 1 / 2) * (cothTail t2 - cothTail (2 * r)) +
            (1 / 2) * ((2 * r - t2) / 2 + ((2 * r) ^ 2 - t2 ^ 2) / 16 -
              4 * lam * (Real.sinh (2 * r / 2) - Real.sinh (t2 / 2)) +
              σ * ∫ u in Ioc t2 (2 * r), hatK h n v u))) := by
  set E := energy g.1 with hE
  have hE0 : 0 ≤ E := energy_nonnegative g.1
  have h2r : 0 ≤ 2 * r := by linarith
  -- archimedean integral on (0, 2r] plus the tail
  rw [archimedean_real_eq_log_integral_v27, split_at g (2 * r) h2r, tail_eq g r a hr0 hw]
  -- decompose the width integrand
  have hWi : IntegrableOn (widthArchLogIntegrandV26 g) (Ioc 0 (2 * r)) :=
    (width_arch_log_integrableOn_v27 g).mono_set (fun u hu => hu.1)
  have hMi : IntegrableOn (momentLog g) (Ioc 0 (2 * r)) :=
    (moment_log_integrableOn g).mono_set (fun u hu => hu.1)
  have hCKi : IntegrableOn (fun u => cRe g u * hatK h n v u) (Ioc 0 (2 * r)) :=
    ((cRe_continuous g).mul (hatK_continuous h n v)).integrableOn_Ioc
  have hHi := hatIntegrand_integrableOn g lam σ h n v 0 (2 * r) le_rfl
  have hdecomp : (∫ u in Ioc 0 (2 * r), widthArchLogIntegrandV26 g u) =
      (∫ u in Ioc 0 (2 * r), hatIntegrand g lam σ h n v u) +
        lam * (∫ u in Ioc 0 (2 * r), momentLog g u) -
        σ * ∫ u in Ioc 0 (2 * r), cRe g u * hatK h n v u := by
    have hA : IntegrableOn (fun u => hatIntegrand g lam σ h n v u + lam * momentLog g u)
        (Ioc 0 (2 * r)) := hHi.add (hMi.const_mul lam)
    have hB : IntegrableOn (fun u => σ * (cRe g u * hatK h n v u)) (Ioc 0 (2 * r)) :=
      hCKi.const_mul σ
    have hL : IntegrableOn (fun u => lam * momentLog g u) (Ioc 0 (2 * r)) := hMi.const_mul lam
    calc (∫ u in Ioc 0 (2 * r), widthArchLogIntegrandV26 g u)
        = ∫ u in Ioc 0 (2 * r), ((hatIntegrand g lam σ h n v u + lam * momentLog g u) -
            σ * (cRe g u * hatK h n v u)) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro u _
          simp only [hatIntegrand]
          ring
      _ = (∫ u in Ioc 0 (2 * r), (hatIntegrand g lam σ h n v u + lam * momentLog g u)) -
            ∫ u in Ioc 0 (2 * r), σ * (cRe g u * hatK h n v u) := integral_sub hA hB
      _ = _ := by
          rw [integral_add hHi hL, integral_const_mul, integral_const_mul]
  -- moment identity on (0, 2r]
  have hmom : (∫ u in Ioc 0 (2 * r), momentLog g u) = 0 := by
    rw [← integral_zero_beyond (momentLog g) (2 * r) h2r (moment_log_integrableOn g)]
    · exact moment_log_identity g hm
    · intro u hu
      unfold momentLog
      rw [autocorrelation_zero_of_halfWidth g r a u hw hu]
      simp
  -- positive definiteness on (0, 2r]
  have hpd : 0 ≤ ∫ u in Ioc 0 (2 * r), cRe g u * hatK h n v u := by
    have hz : ∀ u, 2 * r < u → cRe g u * hatK h n v u = 0 := by
      intro u hu; simp [cRe_zero g r a u hw hu]
    have hIoi : IntegrableOn (fun u => cRe g u * hatK h n v u) (Ioi 0) := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi h2r]
      apply IntegrableOn.union hCKi
      exact integrableOn_zero.congr_fun (fun u hu => (hz u hu).symm) measurableSet_Ioi
    rw [← integral_zero_beyond (fun u => cRe g u * hatK h n v u) (2 * r) h2r hIoi hz]
    exact hat_posdef_packet g h hh n v
  -- three regions
  have hsplit1 : (∫ u in Ioc 0 (2 * r), hatIntegrand g lam σ h n v u) =
      (∫ u in Ioc 0 t1, hatIntegrand g lam σ h n v u) +
        ∫ u in Ioc t1 (2 * r), hatIntegrand g lam σ h n v u := by
    rw [← Ioc_union_Ioc_eq_Ioc ht1.le (by linarith), setIntegral_union
      (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hatIntegrand_integrableOn g lam σ h n v 0 t1 le_rfl)
      (hatIntegrand_integrableOn g lam σ h n v t1 (2 * r) ht1.le)]
  have hsplit2 : (∫ u in Ioc t1 (2 * r), hatIntegrand g lam σ h n v u) =
      (∫ u in Ioc t1 t2, hatIntegrand g lam σ h n v u) +
        ∫ u in Ioc t2 (2 * r), hatIntegrand g lam σ h n v u := by
    rw [← Ioc_union_Ioc_eq_Ioc ht12 ht2', setIntegral_union
      (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hatIntegrand_integrableOn g lam σ h n v t1 t2 ht1.le)
      (hatIntegrand_integrableOn g lam σ h n v t2 (2 * r) (by linarith))]
  have hkc : Continuous (hatK h n v) := hatK_continuous h n v
  have hR1 : (∫ u in Ioc 0 t1, hatIntegrand g lam σ h n v u) ≤
      E * (t1 / 2 + t1 ^ 2 / 16 - 4 * lam * Real.sinh (t1 / 2) +
        σ * ∫ u in Ioc 0 t1, hatK h n v u) := by
    rw [← region_integral_zero g lam σ h n v t1 ht1.le]
    apply setIntegral_mono_on (hatIntegrand_integrableOn g lam σ h n v 0 t1 le_rfl) _
      measurableSet_Ioc
    · intro u hu
      exact hatIntegrand_le_one g lam σ h n v u hu.1 (by linarith [hu.2])
        (hQ u ⟨hu.1, by linarith [hu.2]⟩)
    · exact ((continuous_const.mul ((continuous_const.add (continuous_id.div_const 8)).sub
        (continuous_const.mul (Real.continuous_cosh.comp (continuous_id.div_const 2)))
        |>.add (continuous_const.mul hkc)))).integrableOn_Ioc
  have hmaj : ∀ (c₀ lo hi : ℝ), 0 < lo → lo ≤ hi → 0 ≤ c₀ →
      IntegrableOn (fun u => -(1 - c₀) * E * (1 / Real.sinh u) +
        c₀ * E * (1 / 2 + u / 8 - 2 * lam * Real.cosh (u / 2) + σ * hatK h n v u)) (Ioc lo hi) := by
    intro c₀ lo hi hlo _ _
    have hs := (integrableOn_inv_sinh_Ioc lo hi hlo).const_mul (-(1 - c₀) * E)
    have hrest : IntegrableOn (fun u : ℝ => c₀ * E * (1 / 2 + u / 8 - 2 * lam * Real.cosh (u / 2) +
        σ * hatK h n v u)) (Ioc lo hi) :=
      ((continuous_const.mul ((continuous_const.add (continuous_id.div_const 8)).sub
        (continuous_const.mul (Real.continuous_cosh.comp (continuous_id.div_const 2)))
        |>.add (continuous_const.mul hkc)))).integrableOn_Ioc
    exact hs.add hrest
  have hR2 : (∫ u in Ioc t1 t2, hatIntegrand g lam σ h n v u) ≤
      -(1 - 71 / 100) * E * (cothTail t1 - cothTail t2) +
        (71 / 100) * E * ((t2 - t1) / 2 + (t2 ^ 2 - t1 ^ 2) / 16 -
          4 * lam * (Real.sinh (t2 / 2) - Real.sinh (t1 / 2)) +
          σ * ∫ u in Ioc t1 t2, hatK h n v u) := by
    rw [← region_integral g lam σ h n v t1 t2 (71 / 100) ht1 ht12]
    apply setIntegral_mono_on (hatIntegrand_integrableOn g lam σ h n v t1 t2 ht1.le)
      (hmaj _ _ _ ht1 ht12 (by norm_num)) measurableSet_Ioc
    intro u hu
    have hu0 : 0 < u := lt_trans ht1 hu.1
    have hc : cRe g u ≤ (71 / 100) * E := by
      unfold cRe
      exact le_trans (Complex.re_le_norm _)
        (three_cell_logCorrelation g r a u hw (by linarith [hu.1]) hu0)
    exact hatIntegrand_le g lam σ h n v u (71 / 100) hu0 (by linarith [hu.2]) (by norm_num)
      (hQ u ⟨hu0, by linarith [hu.2]⟩) hc
  have hR3 : (∫ u in Ioc t2 (2 * r), hatIntegrand g lam σ h n v u) ≤
      -(1 - 1 / 2) * E * (cothTail t2 - cothTail (2 * r)) +
        (1 / 2) * E * ((2 * r - t2) / 2 + ((2 * r) ^ 2 - t2 ^ 2) / 16 -
          4 * lam * (Real.sinh (2 * r / 2) - Real.sinh (t2 / 2)) +
          σ * ∫ u in Ioc t2 (2 * r), hatK h n v u) := by
    have ht2p : 0 < t2 := by linarith
    rw [← region_integral g lam σ h n v t2 (2 * r) (1 / 2) ht2p ht2']
    apply setIntegral_mono_on (hatIntegrand_integrableOn g lam σ h n v t2 (2 * r) ht2p.le)
      (hmaj _ _ _ ht2p ht2' (by norm_num)) measurableSet_Ioc
    intro u hu
    have hu0 : 0 < u := lt_trans ht2p hu.1
    have hc : cRe g u ≤ (1 / 2) * E := by
      unfold cRe
      have := half_cap_logCorrelation g r a u hw (by linarith [hu.1])
      linarith [Complex.re_le_norm (logCorrelationV25 g u)]
    exact hatIntegrand_le g lam σ h n v u (1 / 2) hu0 (by linarith [hu.2]) (by norm_num)
      (hQ u ⟨hu0, hu.2⟩) hc
  rw [hdecomp, hmom, hsplit1, hsplit2]
  have hσpd := mul_nonneg hσ hpd
  nlinarith

/-- The hat gain: `Re RHS(A) ≤ hatGain · E` below `log 2`. -/
def hatGain (r lam σ h t1 t2 : ℝ) (n : ℕ) (v : ℕ → ℝ) : ℝ :=
  diagonalKappaV21 - cothTail (2 * r)
    + (t1 / 2 + t1 ^ 2 / 16 - 4 * lam * Real.sinh (t1 / 2) + σ * ∫ u in Ioc 0 t1, hatK h n v u)
    + (-(1 - 71 / 100) * (cothTail t1 - cothTail t2) +
        (71 / 100) * ((t2 - t1) / 2 + (t2 ^ 2 - t1 ^ 2) / 16 -
          4 * lam * (Real.sinh (t2 / 2) - Real.sinh (t1 / 2)) +
          σ * ∫ u in Ioc t1 t2, hatK h n v u))
    + (-(1 - 1 / 2) * (cothTail t2 - cothTail (2 * r)) +
        (1 / 2) * ((2 * r - t2) / 2 + ((2 * r) ^ 2 - t2 ^ 2) / 16 -
          4 * lam * (Real.sinh (2 * r / 2) - Real.sinh (t2 / 2)) +
          σ * ∫ u in Ioc t2 (2 * r), hatK h n v u))

/-- **Hat diagonal.**  Below `log 2`, `Re RHS(A) ≤ hatGain · E`. -/
theorem hat_diagonal (g : WeilCompactSmoothGV1) (r a lam σ h t1 t2 : ℝ) (n : ℕ)
    (v : ℕ → ℝ) (hr0 : 0 < r) (hr1 : 2 * r ≤ 1) (hlog : 2 * r < Real.log 2) (hh : 0 ≤ h)
    (hσ : 0 ≤ σ) (ht1 : 0 < t1) (ht1' : 2 * r ≤ 3 * t1) (ht12 : t1 ≤ t2) (ht2 : r ≤ t2)
    (ht2' : t2 ≤ 2 * r) (hw : HalfWidthAt g r a) (hm : WeilMomentConditionsV1 g)
    (hQ : ∀ u ∈ Ioc 0 (2 * r), 0 ≤ kernelQ lam σ h n v u) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤
      hatGain r lam σ h t1 t2 n v * energy g.1 := by
  have hp := prime_sum_zero_of_halfWidth g r a hw hlog
  have hb := hat_arch_budget g r a lam σ h t1 t2 n v hr0 hr1 hh hσ ht1 ht1' ht12 ht2 ht2' hw hm hQ
  change (B g g).re ≤ _
  rw [actual_diagonal_rhs_decomposition g hp]
  unfold hatGain
  nlinarith [energy_nonnegative g.1]

end AEGIS.RHHatBudgetV13

#print axioms AEGIS.RHHatBudgetV13.hat_posdef_packet
#print axioms AEGIS.RHHatBudgetV13.hat_arch_budget
#print axioms AEGIS.RHHatBudgetV13.hat_diagonal
