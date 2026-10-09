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

import WeilMomentKillerConstructionV1
import ZeroCriticalStripV1
import ZeroHeightSummabilityBridgeV1
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
AEGIS Ω — targeted moment-zero log witness V11.

For each canonical nontrivial zeta zero rho, this module builds a compactly
supported smooth complex log-test

  psi_rho(u) = psi0(u) * exp(-u rho)

and applies the same D(D+1) moment-killer already used by AEGIS:

  phi_rho = psi_rho' + psi_rho''.

It proves:
* integral phi_rho = 0;
* integral phi_rho * exp(u) = 0;
* integral exp(u rho) * phi_rho(u)
    = rho (rho - 1) * integral psi0;
* the last quantity is nonzero for every nontrivial zeta zero.

This is the missing targeted residue witness in log coordinates.  Transport to
the multiplicative Weil packet is a separate thin bridge.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter MeasureTheory Complex
open scoped Topology ContDiff

set_option autoImplicit false
noncomputable section

namespace AEGIS.RestrictedWeilCriterionTargetWitnessV11

open AEGIS.WeilMomentKillerConstructionV1

/-- Complex modulation of the existing compactly supported log bump. -/
def TargetPsiV11 (rho : ℂ) (u : ℝ) : ℂ :=
  (psi0 u : ℂ) * Complex.exp (-(u • rho))

/-- Complex D(D+1) moment killer. -/
def TargetPhiV11 (rho : ℂ) (u : ℝ) : ℂ :=
  deriv (TargetPsiV11 rho) u +
    deriv (deriv (TargetPsiV11 rho)) u

private theorem contDiff_deriv_complex_v11
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (deriv f) := by
  exact
    ((contDiff_infty_iff_deriv (𝕜 := ℝ) (f := f)).mp hf).2

theorem targetPsi_contDiff_v11 (rho : ℂ) :
    ContDiff ℝ ∞ (TargetPsiV11 rho) := by
  unfold TargetPsiV11
  exact
    (Complex.ofRealCLM.contDiff.comp psi0_contDiff).mul
      (by fun_prop)

theorem targetPsi_hasCompactSupport_v11 (rho : ℂ) :
    HasCompactSupport (TargetPsiV11 rho) := by
  have hbase' :
      HasCompactSupport (Complex.ofReal ∘ psi0) :=
    psi0_hasCompactSupport.comp_left (by norm_num)
  have hbase :
      HasCompactSupport (fun u : ℝ => (psi0 u : ℂ)) := by
    simpa [Function.comp_def] using hbase'
  exact hbase.mul_right

theorem targetPhi_contDiff_v11 (rho : ℂ) :
    ContDiff ℝ ∞ (TargetPhiV11 rho) := by
  unfold TargetPhiV11
  exact
    (contDiff_deriv_complex_v11 (targetPsi_contDiff_v11 rho)).add
      (contDiff_deriv_complex_v11
        (contDiff_deriv_complex_v11 (targetPsi_contDiff_v11 rho)))

theorem targetPhi_hasCompactSupport_v11 (rho : ℂ) :
    HasCompactSupport (TargetPhiV11 rho) := by
  unfold TargetPhiV11
  have h := targetPsi_hasCompactSupport_v11 rho
  exact h.deriv.add h.deriv.deriv

/-- Complex-valued compact-support derivative integral. -/
private theorem integral_deriv_eq_zero_complex_v11
    {F : ℝ → ℂ}
    (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) :
    ∫ u : ℝ, deriv F u = 0 := by
  have hint : Integrable (deriv F) :=
    (hF.continuous_deriv le_rfl).integrable_of_hasCompactSupport hFc.deriv
  have h :=
    intervalIntegral.integral_Iic_add_Ioi
      (f := deriv F) (b := (0 : ℝ))
      hint.integrableOn hint.integrableOn
  rw [HasCompactSupport.integral_Iic_deriv_eq hF hFc 0,
    HasCompactSupport.integral_Ioi_deriv_eq hF hFc 0] at h
  simpa using h.symm

/-- First exact moment: D(D+1) integrates to zero. -/
theorem targetPhi_integral_zero_v11 (rho : ℂ) :
    ∫ u : ℝ, TargetPhiV11 rho u = 0 := by
  let F : ℝ → ℂ := fun u =>
    TargetPsiV11 rho u + deriv (TargetPsiV11 rho) u
  have hF : ContDiff ℝ 1 F := by
    dsimp [F]
    exact
      ((targetPsi_contDiff_v11 rho).of_le (by simp)).add
        ((contDiff_deriv_complex_v11
          (targetPsi_contDiff_v11 rho)).of_le (by simp))
  have hFc : HasCompactSupport F := by
    dsimp [F]
    have h := targetPsi_hasCompactSupport_v11 rho
    exact h.add h.deriv
  have hder : deriv F = TargetPhiV11 rho := by
    funext u
    have hd :
        HasDerivAt F
          (deriv (TargetPsiV11 rho) u +
            deriv (deriv (TargetPsiV11 rho)) u) u := by
      dsimp [F]
      exact
        ((targetPsi_contDiff_v11 rho).differentiable
          (by simp) u).hasDerivAt.add
        ((contDiff_deriv_complex_v11
          (targetPsi_contDiff_v11 rho)).differentiable
          (by simp) u).hasDerivAt
    rw [hd.deriv]
    rfl
  rw [← hder]
  exact integral_deriv_eq_zero_complex_v11 hF hFc

/-- Second exact moment: multiplying D(D+1) by exp(u) gives a total derivative. -/
theorem targetPhi_exp_integral_zero_v11 (rho : ℂ) :
    ∫ u : ℝ, TargetPhiV11 rho u * (Real.exp u : ℂ) = 0 := by
  let F : ℝ → ℂ := fun u =>
    deriv (TargetPsiV11 rho) u * (Real.exp u : ℂ)
  have hF : ContDiff ℝ 1 F := by
    dsimp [F]
    exact
      ((contDiff_deriv_complex_v11
        (targetPsi_contDiff_v11 rho)).of_le (by simp)).mul
      (Complex.ofRealCLM.contDiff.comp
        (show ContDiff ℝ 1 Real.exp from Real.contDiff_exp))
  have hFc : HasCompactSupport F := by
    dsimp [F]
    exact (targetPsi_hasCompactSupport_v11 rho).deriv.mul_right
  have hder :
      deriv F =
        fun u => TargetPhiV11 rho u * (Real.exp u : ℂ) := by
    funext u
    have h1 :=
      ((contDiff_deriv_complex_v11
        (targetPsi_contDiff_v11 rho)).differentiable
          (by simp) u).hasDerivAt
    have h2 : HasDerivAt (fun x : ℝ => (Real.exp x : ℂ))
        (Real.exp u : ℂ) u :=
      (Real.hasDerivAt_exp u).ofReal_comp
    have hd := h1.mul h2
    change
      deriv
          ((deriv (TargetPsiV11 rho)) *
            (fun x : ℝ => (Real.exp x : ℂ))) u =
        TargetPhiV11 rho u * (Real.exp u : ℂ)
    rw [hd.deriv]
    unfold TargetPhiV11
    ring
  rw [← hder]
  exact integral_deriv_eq_zero_complex_v11 hF hFc

/-- First derivative of the targeted modulation. -/
theorem targetPsi_deriv_v11 (rho : ℂ) (u : ℝ) :
    deriv (TargetPsiV11 rho) u =
      (((deriv psi0 u : ℝ) : ℂ) -
        rho * (psi0 u : ℂ)) *
        Complex.exp (-(u • rho)) := by
  have hpsiR :=
    (psi0_contDiff.differentiable (by simp) u).hasDerivAt
  have hpsi :
      HasDerivAt (fun x : ℝ => (psi0 x : ℂ))
        ((deriv psi0 u : ℝ) : ℂ) u :=
    hpsiR.ofReal_comp
  have hlin :
      HasDerivAt (fun x : ℝ => -(x • rho)) (-rho) u := by
    simpa using ((hasDerivAt_id' u).smul_const rho).fun_neg
  have hexp := hlin.cexp
  have hprod := hpsi.mul hexp
  calc
    deriv (TargetPsiV11 rho) u =
        ((deriv psi0 u : ℝ) : ℂ) * Complex.exp (-(u • rho)) +
          (psi0 u : ℂ) * (Complex.exp (-(u • rho)) * (-rho)) := by
      change
        deriv
            ((fun x : ℝ => (psi0 x : ℂ)) *
              (fun x : ℝ => Complex.exp (-(x • rho)))) u =
          _
      simpa [smul_eq_mul] using hprod.deriv
    _ = ((((deriv psi0 u : ℝ) : ℂ) -
          rho * (psi0 u : ℂ)) *
          Complex.exp (-(u • rho))) := by
      ring

/-- Second derivative of the targeted modulation. -/
theorem targetPsi_second_deriv_v11 (rho : ℂ) (u : ℝ) :
    deriv (deriv (TargetPsiV11 rho)) u =
      (((deriv (deriv psi0) u : ℝ) : ℂ) -
        2 * rho * ((deriv psi0 u : ℝ) : ℂ) +
        rho ^ 2 * (psi0 u : ℂ)) *
        Complex.exp (-(u • rho)) := by
  have hpsi1R :=
    ((contDiff_deriv psi0_contDiff).differentiable
      (by simp) u).hasDerivAt
  have hpsi1 :
      HasDerivAt (fun x : ℝ => ((deriv psi0 x : ℝ) : ℂ))
        ((deriv (deriv psi0) u : ℝ) : ℂ) u :=
    hpsi1R.ofReal_comp
  have hpsi0R :=
    (psi0_contDiff.differentiable (by simp) u).hasDerivAt
  have hpsi0 :
      HasDerivAt (fun x : ℝ => (psi0 x : ℂ))
        ((deriv psi0 u : ℝ) : ℂ) u :=
    hpsi0R.ofReal_comp
  have hq :
      HasDerivAt
        (fun x : ℝ =>
          ((deriv psi0 x : ℝ) : ℂ) -
            rho * (psi0 x : ℂ))
        (((deriv (deriv psi0) u : ℝ) : ℂ) -
          rho * ((deriv psi0 u : ℝ) : ℂ)) u :=
    hpsi1.sub (hpsi0.const_mul rho)
  have hlin :
      HasDerivAt (fun x : ℝ => -(x • rho)) (-rho) u := by
    simpa using ((hasDerivAt_id' u).smul_const rho).fun_neg
  have hexp := hlin.cexp
  have hprod := hq.mul hexp
  have hfirst := targetPsi_deriv_v11 rho
  have hfun :
      deriv (TargetPsiV11 rho) =
        fun x : ℝ =>
          (((deriv psi0 x : ℝ) : ℂ) -
            rho * (psi0 x : ℂ)) *
            Complex.exp (-(x • rho)) := by
    funext x
    exact hfirst x
  rw [hfun]
  calc
    deriv
        (fun x : ℝ =>
          (((deriv psi0 x : ℝ) : ℂ) -
            rho * (psi0 x : ℂ)) *
            Complex.exp (-(x • rho))) u =
      (((deriv (deriv psi0) u : ℝ) : ℂ) -
          rho * ((deriv psi0 u : ℝ) : ℂ)) *
          Complex.exp (-(u • rho)) +
        (((deriv psi0 u : ℝ) : ℂ) -
          rho * (psi0 u : ℂ)) *
          (Complex.exp (-(u • rho)) * (-rho)) := by
      change
        deriv
            ((fun x : ℝ =>
                (((deriv psi0 x : ℝ) : ℂ) -
                  rho * (psi0 x : ℂ))) *
              (fun x : ℝ => Complex.exp (-(x • rho)))) u =
          _
      simpa [smul_eq_mul] using hprod.deriv
    _ =
      ((((deriv (deriv psi0) u : ℝ) : ℂ) -
        2 * rho * ((deriv psi0 u : ℝ) : ℂ) +
        rho ^ 2 * (psi0 u : ℂ)) *
        Complex.exp (-(u • rho))) := by
      ring

/-- After multiplying by exp(u rho), the targeted moment-killer becomes a
finite differential expression in the original real bump. -/
theorem targetPhi_weighted_pointwise_v11 (rho : ℂ) (u : ℝ) :
    Complex.exp (u • rho) * TargetPhiV11 rho u =
      ((deriv (deriv psi0) u : ℝ) : ℂ) +
      (1 - 2 * rho) * ((deriv psi0 u : ℝ) : ℂ) +
      (rho ^ 2 - rho) * (psi0 u : ℂ) := by
  unfold TargetPhiV11
  rw [targetPsi_deriv_v11, targetPsi_second_deriv_v11]
  have hexp :
      Complex.exp (u • rho) *
          Complex.exp (-(u • rho)) = 1 := by
    rw [← Complex.exp_add]
    simp
  calc
    _ =
        (Complex.exp (u • rho) * Complex.exp (-(u • rho))) *
          (((deriv (deriv psi0) u : ℝ) : ℂ) +
            (1 - 2 * rho) * ((deriv psi0 u : ℝ) : ℂ) +
            (rho ^ 2 - rho) * (psi0 u : ℂ)) := by
          ring
    _ = _ := by
      rw [hexp]
      ring

/-- Exact targeted transform. -/
theorem targetPhi_weighted_integral_v11 (rho : ℂ) :
    (∫ u : ℝ,
      Complex.exp (u • rho) * TargetPhiV11 rho u) =
      (rho ^ 2 - rho) *
        ((∫ u : ℝ, psi0 u : ℝ) : ℂ) := by
  have h0 : Integrable psi0 :=
    psi0_contDiff.continuous.integrable_of_hasCompactSupport
      psi0_hasCompactSupport
  have h1 : Integrable (deriv psi0) :=
    ((contDiff_deriv psi0_contDiff).continuous).integrable_of_hasCompactSupport
      psi0_hasCompactSupport.deriv
  have h2cont : Continuous (deriv (deriv psi0)) :=
    (contDiff_deriv (contDiff_deriv psi0_contDiff)).continuous
  have h2 : Integrable (deriv (deriv psi0)) :=
    h2cont.integrable_of_hasCompactSupport
      psi0_hasCompactSupport.deriv.deriv

  have hi1 : ∫ u : ℝ, deriv psi0 u = 0 :=
    integral_deriv_eq_zero
      (psi0_contDiff.of_le (by simp))
      psi0_hasCompactSupport
  have hi2 : ∫ u : ℝ, deriv (deriv psi0) u = 0 :=
    integral_deriv_eq_zero
      ((contDiff_deriv psi0_contDiff).of_le (by simp))
      psi0_hasCompactSupport.deriv

  calc
    (∫ u : ℝ,
      Complex.exp (u • rho) * TargetPhiV11 rho u)
      =
    ∫ u : ℝ,
      (((deriv (deriv psi0) u : ℝ) : ℂ) +
      (1 - 2 * rho) * ((deriv psi0 u : ℝ) : ℂ) +
      (rho ^ 2 - rho) * (psi0 u : ℂ)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall
          (targetPhi_weighted_pointwise_v11 rho)
    _ =
      (∫ u : ℝ, ((deriv (deriv psi0) u : ℝ) : ℂ)) +
      (1 - 2 * rho) *
        (∫ u : ℝ, ((deriv psi0 u : ℝ) : ℂ)) +
      (rho ^ 2 - rho) *
        (∫ u : ℝ, (psi0 u : ℂ)) := by
          have h2c : Integrable (fun u : ℝ =>
              ((deriv (deriv psi0) u : ℝ) : ℂ)) := h2.ofReal
          have h1c : Integrable (fun u : ℝ =>
              (1 - 2 * rho) * ((deriv psi0 u : ℝ) : ℂ)) :=
            h1.ofReal.const_mul (1 - 2 * rho)
          have h0c : Integrable (fun u : ℝ =>
              (rho ^ 2 - rho) * (psi0 u : ℂ)) :=
            h0.ofReal.const_mul (rho ^ 2 - rho)
          calc
            _ = (∫ u : ℝ,
                  ((deriv (deriv psi0) u : ℝ) : ℂ) +
                    (1 - 2 * rho) * ((deriv psi0 u : ℝ) : ℂ)) +
                ∫ u : ℝ, (rho ^ 2 - rho) * (psi0 u : ℂ) := by
                  exact integral_add (h2c.add h1c) h0c
            _ = ((∫ u : ℝ, ((deriv (deriv psi0) u : ℝ) : ℂ)) +
                  ∫ u : ℝ, (1 - 2 * rho) * ((deriv psi0 u : ℝ) : ℂ)) +
                ∫ u : ℝ, (rho ^ 2 - rho) * (psi0 u : ℂ) := by
                  rw [integral_add h2c h1c]
            _ = _ := by
                  rw [integral_const_mul, integral_const_mul]
    _ =
      (rho ^ 2 - rho) *
        ((∫ u : ℝ, psi0 u : ℝ) : ℂ) := by
          rw [integral_complex_ofReal, integral_complex_ofReal,
            integral_complex_ofReal, hi1, hi2]
          simp

/-- The existing bump has strictly positive total mass. -/
theorem psi0_integral_pos_v11 :
    0 < ∫ u : ℝ, psi0 u := by
  simpa [psi0] using
    (ubump.integral_pos (μ := volume))

/-- Generic nonvanishing form: the targeted transform is nonzero at
every spectral parameter distinct from 0 and 1. -/
theorem targetPhi_weighted_integral_ne_zero_of_ne_zero_one_v11
    (rho : ℂ) (hr0 : rho ≠ 0) (hr1 : rho ≠ 1) :
    (∫ u : ℝ,
      Complex.exp (u • rho) * TargetPhiV11 rho u) ≠ 0 := by
  rw [targetPhi_weighted_integral_v11]
  have hpoly : rho ^ 2 - rho ≠ 0 := by
    rw [show rho ^ 2 - rho = rho * (rho - 1) by ring]
    exact mul_ne_zero hr0 (sub_ne_zero.mpr hr1)
  have hmassR : (∫ u : ℝ, psi0 u) ≠ 0 :=
    ne_of_gt psi0_integral_pos_v11
  have hmassC : (((∫ u : ℝ, psi0 u : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hmassR
  exact mul_ne_zero hpoly hmassC

/-- Specialization to every canonical nontrivial zeta zero. -/
theorem targetPhi_weighted_integral_ne_zero_v11
    (rho : RiemannNontrivialZeroIndexV2) :
    (∫ u : ℝ,
      Complex.exp (u • rho.1) * TargetPhiV11 rho.1 u) ≠ 0 := by
  have hstrip :=
    riemann_zeta_nontrivial_zero_critical_strip_v1
      rho.2.1 rho.2.2
  have hr0 : rho.1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hstrip.1]
  have hr1 : rho.1 ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hstrip.2]
  exact
    targetPhi_weighted_integral_ne_zero_of_ne_zero_one_v11
      rho.1 hr0 hr1

end AEGIS.RestrictedWeilCriterionTargetWitnessV11

#print axioms AEGIS.RestrictedWeilCriterionTargetWitnessV11.targetPhi_integral_zero_v11
#print axioms AEGIS.RestrictedWeilCriterionTargetWitnessV11.targetPhi_exp_integral_zero_v11
#print axioms AEGIS.RestrictedWeilCriterionTargetWitnessV11.targetPhi_weighted_integral_v11
#print axioms AEGIS.RestrictedWeilCriterionTargetWitnessV11.targetPhi_weighted_integral_ne_zero_v11
