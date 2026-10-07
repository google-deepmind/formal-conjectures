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

import WeilArchimedeanCorrectionV10
import WeilFixedLineGammaAssemblyV10
import WeilArchimedeanConvergenceV1
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
AEGIS Ω — fixed-line gamma x-space normalization V10.

This module performs the two remaining changes of variables in the normalized
gamma term:

  u = 2v,   x = exp v.

It then uses the repository's existing rational Archimedean integrand identity
and the exact correction integral

  ∫_1^∞ dx / (x(x+1)) = log 2

to obtain the repository-native Archimedean expression.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Topology

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilFixedLineGammaXSpaceV10

open AEGIS.WeilArchimedeanCorrectionV10
open AEGIS.WeilFixedLineGammaAssemblyV10

local notation "γ" => Real.eulerMascheroniConstant

/-- The exact u-space integrand produced by V10 Fubini assembly. -/
def WeilGammaLogIntegrandV10
    (f : WeilCompactSmoothGV1) (u : ℝ) : ℂ :=
  (Complex.exp (-(u : ℂ)) * (2 * f.1 1) -
      (WeilPairedTestV8 f).1 (Real.exp (u / 2))) /
    (1 - Complex.exp (-(u : ℂ)))

/-- The x-space integrand after u=2v and x=exp(v), including the Jacobian. -/
def WeilGammaXIntegrandV10
    (f : WeilCompactSmoothGV1) (x : ℝ) : ℂ :=
  (((2 : ℂ) * f.1 1) / (x : ℂ) -
      (x : ℂ) * (WeilPairedTestV8 f).1 x) /
    ((x : ℂ) ^ 2 - 1)

/-- The elementary x-space correction separated from the repository
Archimedean integrand. -/
def WeilGammaCorrectionXIntegrandV10
    (f : WeilCompactSmoothGV1) (x : ℝ) : ℂ :=
  ((2 : ℂ) * f.1 1) *
    ((1 / (x * (x + 1)) : ℝ) : ℂ)

/-- Pointwise identity underlying u=2v, x=exp(v). -/
theorem gamma_log_two_mul_eq_exp_smul_x_v10
    (f : WeilCompactSmoothGV1) {v : ℝ} (hv : 0 < v) :
    WeilGammaLogIntegrandV10 f (2 * v) =
      Real.exp v • WeilGammaXIntegrandV10 f (Real.exp v) := by
  let x : ℝ := Real.exp v
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  have hxgt : 1 < x := by
    dsimp [x]
    have h := Real.exp_lt_exp.mpr hv
    rwa [Real.exp_zero] at h
  have hxC0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxpos.ne'
  have hx2gt : (1 : ℝ) < x ^ 2 := by
    nlinarith
  have hx2neR : x ^ 2 ≠ 1 := ne_of_gt hx2gt
  have hx2neC : (x : ℂ) ^ 2 ≠ 1 := by
    exact_mod_cast hx2neR
  have hxden : (x : ℂ) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hx2neC
  have hexpnegR :
      Real.exp (-(2 * v)) = (x⁻¹) ^ 2 := by
    dsimp [x]
    rw [show -(2 * v) = (-v) + (-v) by ring, Real.exp_add,
      Real.exp_neg]
    ring
  have hexpneg :
      Complex.exp (-(((2 * v : ℝ) : ℂ))) =
        ((x : ℂ)⁻¹) ^ 2 := by
    have hcast :=
      congrArg (fun r : ℝ => (r : ℂ)) hexpnegR
    simpa only [Complex.ofReal_exp, Complex.ofReal_neg,
      Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_inv, Complex.ofReal_pow] using hcast
  have hexphalf :
      Real.exp ((2 * v) / 2) = x := by
    dsimp [x]
    congr 1
    ring
  unfold WeilGammaLogIntegrandV10 WeilGammaXIntegrandV10
  rw [hexpneg, hexphalf, Complex.real_smul]
  have hxe : Real.exp v = x := rfl
  rw [hxe]
  have hxden' : (-1 + (x : ℂ) ^ 2) ≠ 0 := by
    rw [show (-1 + (x : ℂ) ^ 2) = (x : ℂ) ^ 2 - 1 by ring]
    exact hxden
  have hxinv : (1 - ((x : ℂ)⁻¹) ^ 2) ≠ 0 := by
    rw [show (1 - ((x : ℂ)⁻¹) ^ 2) = ((x : ℂ) ^ 2 - 1) / (x : ℂ) ^ 2 by
      field_simp]
    exact div_ne_zero hxden (pow_ne_zero 2 hxC0)
  field_simp

/-- Half of the u-integral is exactly the x-space integral. -/
theorem half_gamma_log_integral_eq_x_integral_v10
    (f : WeilCompactSmoothGV1) :
    (1 / 2 : ℂ) *
        (∫ u : ℝ in Ioi (0 : ℝ), WeilGammaLogIntegrandV10 f u) =
      ∫ x : ℝ in Ioi (1 : ℝ), WeilGammaXIntegrandV10 f x := by
  have hscale :=
    integral_comp_mul_left_Ioi'
      (WeilGammaLogIntegrandV10 f) 0
      (show (0 : ℝ) < 2 by norm_num)
  simp only [mul_zero, Complex.real_smul] at hscale
  calc
    (1 / 2 : ℂ) *
        (∫ u : ℝ in Ioi (0 : ℝ), WeilGammaLogIntegrandV10 f u)
      =
        ∫ v : ℝ in Ioi (0 : ℝ),
          WeilGammaLogIntegrandV10 f (2 * v) := by
            rw [← hscale]
            push_cast
            ring
    _ =
        ∫ v : ℝ in Ioi (0 : ℝ),
          Real.exp v • WeilGammaXIntegrandV10 f (Real.exp v) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro v hv
            exact gamma_log_two_mul_eq_exp_smul_x_v10 f hv
    _ =
        ∫ x : ℝ in Ioi (1 : ℝ),
          WeilGammaXIntegrandV10 f x := by
            simpa using integral_comp_exp_Ioi
              (WeilGammaXIntegrandV10 f) 0

/-- Repository-native decomposition of the x-space gamma integrand. -/
theorem gamma_x_integrand_eq_neg_arch_sub_correction_v10
    (f : WeilCompactSmoothGV1) {x : ℝ} (hx : 1 < x) :
    WeilGammaXIntegrandV10 f x =
      -WeilArchimedeanIntegrandV1 f.1 x -
        WeilGammaCorrectionXIntegrandV10 f x := by
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x + 1 ≠ 0 := by linarith
  have hx2 : x ^ 2 - 1 ≠ 0 := by nlinarith
  rw [WeilGammaXIntegrandV10,
    weil_archimedean_integrand_rational_v1 f.1 hx,
    weil_paired_test_apply_v8]
  unfold WeilReciprocalFnV8 WeilGammaCorrectionXIntegrandV10
  push_cast
  have hx0C : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0
  have hx1C : (x : ℂ) + 1 ≠ 0 := by exact_mod_cast hx1
  have hx2C : (x : ℂ) ^ 2 - 1 ≠ 0 := by exact_mod_cast hx2
  have hx2C' : (-1 + (x : ℂ) ^ 2) ≠ 0 := by
    rw [show (-1 + (x : ℂ) ^ 2) = (x : ℂ) ^ 2 - 1 by ring]
    exact hx2C
  have hx1C' : (1 + (x : ℂ)) ≠ 0 := by rw [add_comm]; exact hx1C
  field_simp
  ring

theorem gamma_correction_x_integrable_v10
    (f : WeilCompactSmoothGV1) :
    IntegrableOn
      (WeilGammaCorrectionXIntegrandV10 f)
      (Ioi (1 : ℝ)) := by
  unfold WeilGammaCorrectionXIntegrandV10
  exact
    (integrableOn_one_div_mul_one_add_v10.ofReal.const_mul
      ((2 : ℂ) * f.1 1))

theorem gamma_correction_x_integral_v10
    (f : WeilCompactSmoothGV1) :
    (∫ x : ℝ in Ioi (1 : ℝ),
      WeilGammaCorrectionXIntegrandV10 f x) =
      ((2 * Real.log 2 : ℝ) : ℂ) * f.1 1 := by
  unfold WeilGammaCorrectionXIntegrandV10
  rw [integral_const_mul]
  have hI :
      (∫ a : ℝ in Ioi (1 : ℝ), (((1 / (a * (a + 1)) : ℝ)) : ℂ)) =
        (((∫ a : ℝ in Ioi (1 : ℝ), 1 / (a * (a + 1))) : ℝ) : ℂ) :=
    integral_ofReal
  rw [hI, integral_one_div_mul_one_add_v10]
  push_cast
  ring

/-- Exact evaluation of the x-space integrand. -/
theorem gamma_x_integral_eq_arch_v10
    (f : WeilCompactSmoothGV1) :
    (∫ x : ℝ in Ioi (1 : ℝ), WeilGammaXIntegrandV10 f x) =
      -WeilArchimedeanIntegralV1 f.1 -
        ((2 * Real.log 2 : ℝ) : ℂ) * f.1 1 := by
  have harch :=
    weil_compact_smooth_archimedean_integrable_v1 f
  have hcorr :=
    gamma_correction_x_integrable_v10 f
  calc
    (∫ x : ℝ in Ioi (1 : ℝ), WeilGammaXIntegrandV10 f x)
      =
      ∫ x : ℝ in Ioi (1 : ℝ),
        (-WeilArchimedeanIntegrandV1 f.1 x -
          WeilGammaCorrectionXIntegrandV10 f x) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          exact
            gamma_x_integrand_eq_neg_arch_sub_correction_v10
              f hx
    _ =
      (∫ x : ℝ in Ioi (1 : ℝ),
        -WeilArchimedeanIntegrandV1 f.1 x) -
      (∫ x : ℝ in Ioi (1 : ℝ),
        WeilGammaCorrectionXIntegrandV10 f x) := by
          exact integral_sub harch.neg hcorr
    _ =
      -WeilArchimedeanIntegralV1 f.1 -
        ((2 * Real.log 2 : ℝ) : ℂ) * f.1 1 := by
          rw [integral_neg, gamma_correction_x_integral_v10]
          rfl

/-- The normalized half of the (digamma + Euler constant) contribution is
exactly the negative repository Archimedean integral plus the log-2
normalization correction. -/
theorem half_fixed_line_digamma_plus_gamma_eq_arch_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
    (1 / 2 : ℂ) *
      ((1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ,
          (Complex.digamma
            ((((c : ℂ) + (t : ℂ) * I) / 2)) + (γ : ℂ)) *
            WeilPairedMellinProfileV5 f c t) =
      -WeilArchimedeanIntegralV1 f.1 -
        ((2 * Real.log 2 : ℝ) : ℂ) * f.1 1 := by
  have hlog :=
    weil_fixed_line_digamma_plus_gamma_log_integral_v10 f c hc
  have hlog' :
      ((1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ,
          (Complex.digamma
            ((((c : ℂ) + (t : ℂ) * I) / 2)) + (γ : ℂ)) *
            WeilPairedMellinProfileV5 f c t) =
        ∫ u : ℝ in Ioi (0 : ℝ),
          WeilGammaLogIntegrandV10 f u := by
    simpa [WeilGammaLogIntegrandV10] using hlog
  rw [hlog']
  rw [half_gamma_log_integral_eq_x_integral_v10]
  exact gamma_x_integral_eq_arch_v10 f

end AEGIS.WeilFixedLineGammaXSpaceV10

#print axioms AEGIS.WeilFixedLineGammaXSpaceV10.gamma_log_two_mul_eq_exp_smul_x_v10
#print axioms AEGIS.WeilFixedLineGammaXSpaceV10.half_gamma_log_integral_eq_x_integral_v10
#print axioms AEGIS.WeilFixedLineGammaXSpaceV10.gamma_x_integrand_eq_neg_arch_sub_correction_v10
#print axioms AEGIS.WeilFixedLineGammaXSpaceV10.gamma_x_integral_eq_arch_v10
#print axioms AEGIS.WeilFixedLineGammaXSpaceV10.half_fixed_line_digamma_plus_gamma_eq_arch_v10
