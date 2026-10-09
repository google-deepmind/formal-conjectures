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

import RHZeroKernelLaplaceV12
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The unconditional growth boundary of the actual zero kernel

The strict critical strip and absolute coefficient summability imply the
endpoint estimate `exp(-t/2) K_g(t) → 0`. They do not supply an arbitrarily
small exponential rate: the finite symmetric spectrum `{-1/4, 1/4}` satisfies
the same strict strip and summability conditions, but its kernel exceeds every
constant multiple of `exp(t/8)`.

The actual-kernel statement uses AEGIS source
`2c3d041b633147ec97c7ef753aa9d157a47bb9f5`. The finite model is an explicit
counterexample to an inference from strip and summability alone, not a model
of the zeta Euler product or a claim about actual nontrivial zeros.
-/

open Filter Topology Complex

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHGlobalGrowthBoundaryV1

open AEGIS.WeilZeroTwoPointV11 AEGIS.RHZeroKernelLaplaceV12

private theorem endpoint_normalized_kernel_eq_tsum
    (g : WeilCompactSmoothGV1) (t : ℝ) :
    Complex.exp (-((1 / 2 : ℂ) * (t : ℂ))) *
        WeilZeroTranslationKernelV11 g t =
      ∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroCoefficientV11 g rho * Complex.exp ((rho.1 - 1) * (t : ℂ)) := by
  have hs := zero_translation_kernel_summable_v11 g t
  unfold WeilZeroTranslationKernelV11
  rw [← hs.tsum_mul_left]
  apply tsum_congr
  intro rho
  unfold WeilZeroTranslationFactorV11
  calc
    Complex.exp (-((1 / 2 : ℂ) * (t : ℂ))) *
        (WeilZeroCoefficientV11 g rho *
          Complex.exp ((rho.1 - (1 / 2 : ℂ)) * (t : ℂ))) =
        WeilZeroCoefficientV11 g rho *
          (Complex.exp (-((1 / 2 : ℂ) * (t : ℂ))) *
            Complex.exp ((rho.1 - (1 / 2 : ℂ)) * (t : ℂ))) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      ring

/-- The strict strip improves the source endpoint majorant to a little-o
statement for every actual packet, without any moment or sign assumption. -/
theorem actual_kernel_endpoint_decay (g : WeilCompactSmoothGV1) :
    Tendsto (fun t : ℝ => Complex.exp (-((1 / 2 : ℂ) * (t : ℂ))) *
      WeilZeroTranslationKernelV11 g t) atTop (𝓝 0) := by
  have hterm : ∀ rho : RiemannNontrivialZeroIndexV2,
      Tendsto (fun t : ℝ => WeilZeroCoefficientV11 g rho *
        Complex.exp ((rho.1 - 1) * (t : ℂ))) atTop (𝓝 (0 : ℂ)) := by
    intro rho
    have hs := riemann_zeta_nontrivial_zero_critical_strip_v1 rho.2.1 rho.2.2
    have hexp : Tendsto (fun t : ℝ => Complex.exp ((rho.1 - 1) * (t : ℂ)))
        atTop (𝓝 (0 : ℂ)) := by
      apply Complex.tendsto_exp_nhds_zero_iff.mpr
      have hlin0 := tendsto_neg_atTop_atBot.comp
        ((tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).const_mul_atTop
          (sub_pos.mpr hs.2))
      have hlin : Tendsto (fun t : ℝ => -((1 - rho.1.re) * t)) atTop atBot := by
        simpa [Function.comp_def] using hlin0
      convert hlin using 1
      funext t
      simp only [Complex.mul_re, Complex.sub_re, Complex.one_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    simpa only [mul_zero] using hexp.const_mul (WeilZeroCoefficientV11 g rho)
  have hbound : ∀ᶠ t : ℝ in atTop, ∀ rho : RiemannNontrivialZeroIndexV2,
      ‖WeilZeroCoefficientV11 g rho * Complex.exp ((rho.1 - 1) * (t : ℂ))‖ ≤
        ‖WeilZeroCoefficientV11 g rho‖ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht rho
    have hs := riemann_zeta_nontrivial_zero_critical_strip_v1 rho.2.1 rho.2.2
    have hre : ((rho.1 - 1) * (t : ℂ)).re ≤ 0 := by
      simp only [Complex.mul_re, Complex.sub_re, Complex.one_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs.2.le) ht
    rw [norm_mul, Complex.norm_exp]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr hre)
  have hlim := tendsto_tsum_of_dominated_convergence
    (zero_coefficient_norm_summable_v12 g) hterm hbound
  simpa only [tsum_zero, ← endpoint_normalized_kernel_eq_tsum] using hlim

/-- A finite even kernel with two positive coefficients and exponents strictly
inside the same centered strip. -/
def symmetricModelKernel (t : ℝ) : ℝ :=
  (Real.exp (t / 4) + Real.exp (-t / 4)) / 2

/-- The counterexample has the same reflection symmetry and normalized value. -/
theorem symmetric_model_properties :
    symmetricModelKernel 0 = 1 ∧
      (∀ t : ℝ, symmetricModelKernel (-t) = symmetricModelKernel t) ∧
      (-(1 / 2 : ℝ) < -(1 / 4 : ℝ) ∧ (1 / 4 : ℝ) < 1 / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [symmetricModelKernel]
  · intro t
    simp only [symmetricModelKernel, neg_neg]
    ring
  · norm_num

/-- Even the strict endpoint decay of the actual kernel does not imply an
arbitrarily small exponential rate: the finite model has that same decay. -/
theorem symmetric_model_endpoint_decay :
    Tendsto (fun t : ℝ => Real.exp (-t / 2) * symmetricModelKernel t)
      atTop (𝓝 0) := by
  have hdecay : ∀ a : ℝ, 0 < a →
      Tendsto (fun t : ℝ => Real.exp (-(a * t))) atTop (𝓝 0) := by
    intro a ha
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      ((tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).const_mul_atTop ha))
  have hlim := ((hdecay (1 / 4) (by norm_num)).add
    (hdecay (3 / 4) (by norm_num))).div_const 2
  simp only [zero_add, zero_div] at hlim
  convert hlim using 1
  funext t
  unfold symmetricModelKernel
  calc
    Real.exp (-t / 2) * ((Real.exp (t / 4) + Real.exp (-t / 4)) / 2) =
        (Real.exp (-t / 2) * Real.exp (t / 4) +
          Real.exp (-t / 2) * Real.exp (-t / 4)) / 2 := by ring
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2 <;> ring

/-- No constant can give rate `1/8`, despite strict-strip membership,
reflection symmetry, and a finite (hence absolutely summable) spectrum. -/
theorem symmetric_model_exceeds_every_eighth_rate (C : ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧ C * Real.exp (t / 8) < symmetricModelKernel t := by
  let u : ℝ := 2 * |C| + 2
  refine ⟨8 * u, by dsimp [u]; positivity, ?_⟩
  have he : 2 * C < Real.exp u := by
    have hl := Real.add_one_le_exp u
    have hc := le_abs_self C
    dsimp [u] at hl
    linarith
  have hp := Real.exp_pos u
  have hn := Real.exp_pos (-2 * u)
  have hmul : (2 * C) * Real.exp u < Real.exp u * Real.exp u :=
    mul_lt_mul_of_pos_right he hp
  have hhalf : C * Real.exp u < (Real.exp u * Real.exp u) / 2 := by
    nlinarith only [hmul]
  have heq : Real.exp u * Real.exp u = Real.exp (u + u) := by
    rw [← Real.exp_add]
  rw [heq] at hhalf
  have hmain :
      C * Real.exp u <
        (Real.exp (u + u) + Real.exp (-2 * u)) / 2 := by
    nlinarith only [hhalf, hn]
  have h2 : (8 * u) / 4 = u + u := by ring
  have h8 : (8 * u) / 8 = u := by ring
  have hn2 : -(8 * u) / 4 = -2 * u := by ring
  rw [symmetricModelKernel, h8, h2, hn2]
  exact hmain

end AEGIS.RHGlobalGrowthBoundaryV1

#print axioms AEGIS.RHGlobalGrowthBoundaryV1.actual_kernel_endpoint_decay
#print axioms AEGIS.RHGlobalGrowthBoundaryV1.symmetric_model_properties
#print axioms AEGIS.RHGlobalGrowthBoundaryV1.symmetric_model_endpoint_decay
#print axioms AEGIS.RHGlobalGrowthBoundaryV1.symmetric_model_exceeds_every_eighth_rate
