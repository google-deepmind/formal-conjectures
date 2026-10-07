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

import RHKreinZetaBridgeV1

/-!
# Plancherel for packets

For a packet `g` of finite log-width, the critical-line energy is the `L²` norm of its log profile:

  `(1/2π) ∫ Nr g t dt = ∫ ‖Gm g u‖² du`.

Proof: `Gm g` is smooth with compact support, hence Schwartz (`HasCompactSupport.toSchwartzMap`);
Mathlib's `L²` Fourier isometry (`MeasureTheory.Lp.norm_fourier_eq`) and the substitution
`t = 2πν` give the identity.  This identifies the energy `N(g)` of the Krein certificates with the
Hilbert norm in which the Feshbach decomposition is taken.  AUTHORITY_EFFECT = NONE.
-/

open MeasureTheory FourierTransform Complex
open scoped ContDiff SchwartzMap InnerProductSpace
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHPlancherelPacketV1

open AEGIS.WeilCriticalLineKreinFormV1
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHKreinZetaBridgeV1

theorem Gm_hasCompactSupport (g : WeilCompactSmoothGV1) (r a : ℝ) (hw : HalfWidthAt g r a) :
    HasCompactSupport (Gm g) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((subset_tsupport _).trans (Gm_tsupport g r a hw))

/-- `‖ψ‖²_{L²} = ∫ ‖ψ‖²` for a Schwartz function. -/
theorem schwartz_L2_norm_sq (ψ : 𝓢(ℝ, ℂ)) :
    ‖ψ.toLp 2 (volume : Measure ℝ)‖ ^ 2 = ∫ x, ‖ψ x‖ ^ 2 := by
  have h := MeasureTheory.L2.inner_def (𝕜 := ℂ) (ψ.toLp 2 (volume : Measure ℝ))
    (ψ.toLp 2 (volume : Measure ℝ))
  have hae := ψ.coeFn_toLp 2 (volume : Measure ℝ)
  have h2 : (∫ a : ℝ, ⟪(ψ.toLp 2 volume : ℝ → ℂ) a, (ψ.toLp 2 volume : ℝ → ℂ) a⟫_ℂ) =
      ∫ a : ℝ, (((‖ψ a‖ ^ 2 : ℝ)) : ℂ) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with a ha
    rw [ha, inner_self_eq_norm_sq_to_K]; norm_cast
  rw [h2, integral_complex_ofReal] at h
  have h3 := congrArg Complex.re h
  rw [Complex.ofReal_re] at h3
  rw [← h3]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm

theorem energy_eq_L2 (g : WeilCompactSmoothGV1) (r a : ℝ) (hw : HalfWidthAt g r a) :
    (1 / (2 * Real.pi)) * ∫ t : ℝ, Nr g t = ∫ u : ℝ, ‖Gm g u‖ ^ 2 := by
  set ψ : 𝓢(ℝ, ℂ) := (Gm_hasCompactSupport g r a hw).toSchwartzMap (Gm_contDiff g) with hψ
  have hψa : ∀ u, ψ u = Gm g u := fun u => rfl
  -- Plancherel
  have hP := MeasureTheory.Lp.norm_fourier_eq (ψ.toLp 2 (volume : Measure ℝ))
  rw [SchwartzMap.toLp_fourier_eq] at hP
  have h1 := schwartz_L2_norm_sq (𝓕 ψ)
  have h2 := schwartz_L2_norm_sq ψ
  rw [hP] at h1
  have hF : ∀ ν, (𝓕 ψ) ν = 𝓕 (Gm g) ν := fun ν => by
    rw [SchwartzMap.fourier_coe]; rfl
  -- ∫ Nr g t dt = 2π ∫ ‖𝓕 Gm ν‖² dν
  have hsub : (∫ t : ℝ, Nr g t) = (2 * Real.pi) * ∫ ν : ℝ, ‖𝓕 (Gm g) ν‖ ^ 2 := by
    have e : (fun t : ℝ => Nr g t) = fun t => (fun ν => ‖𝓕 (Gm g) ν‖ ^ 2) (t / (2 * Real.pi)) := by
      funext t; rw [Nr_eq, Complex.normSq_eq_norm_sq]
    rw [e, MeasureTheory.Measure.integral_comp_div (fun ν => ‖𝓕 (Gm g) ν‖ ^ 2) (2 * Real.pi),
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), smul_eq_mul]
  rw [hsub, ← mul_assoc, one_div, inv_mul_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), one_mul]
  simp only [hF] at h1
  simp only [hψa] at h2
  rw [← h1, h2]

end AEGIS.RHPlancherelPacketV1

#print axioms AEGIS.RHPlancherelPacketV1.energy_eq_L2
