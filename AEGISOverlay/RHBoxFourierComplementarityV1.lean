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

import AEGISOverlay.RHMultiGeneratorComplementarityV1
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Topology.Algebra.Support

/-!
# Complementarity for actual Fourier transforms of compact interval profiles

This module binds sinc complementarity to the Mathlib Fourier transform,
with angular frequency t represented by -t/(2π). The profiles have compact
support but are not smooth Weil packets. No approximation or sign theorem
is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHBoxFourierComplementarityV1

open AEGIS.RHMultiGeneratorComplementarityV1

open MeasureTheory FourierTransform

/-- The compactly supported interval profile used in the generator experiment. -/
def boxProfile (a : ℝ) : ℝ → ℂ :=
  Set.indicator (Set.Ioc (-a) a) (fun _ => 1)

/-- The interval profiles have genuine compact support. -/
theorem boxProfile_hasCompactSupport (a : ℝ) : HasCompactSupport (boxProfile a) := by
  apply HasCompactSupport.intro (K := Set.Icc (-a) a) isCompact_Icc
  intro u hu
  have hu' : u ∉ Set.Ioc (-a) a := fun h => hu ⟨h.1.le, h.2⟩
  simp [boxProfile, hu']

/-- The angular-frequency integral of an interval is its sinc symbol. -/
theorem box_angular_integral (a t : ℝ) :
    (∫ u in -a..a, Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)) =
      2 * (a : ℂ) * (Real.sinc (a * t) : ℂ) := by
  by_cases ht : t = 0
  · subst t
    simp
    ring
  change (∫ u in -a..a, (fun v : ℝ => Complex.exp ((v : ℂ) * Complex.I)) (t * u)) = _
  rw [intervalIntegral.integral_comp_mul_left
    (fun v : ℝ => Complex.exp ((v : ℂ) * Complex.I)) ht, mul_neg,
    integral_exp_mul_I_eq_sinc]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul]
  rw [mul_comm t a]
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  field_simp [htc]

/-- The actual Mathlib Fourier transform of the compact interval profile,
with the same angular-frequency conversion as the critical Mellin bridge. -/
theorem fourier_boxProfile_scaled {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    𝓕 (boxProfile a) (-t / (2 * Real.pi)) =
      2 * (a : ℂ) * (Real.sinc (a * t) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hphase (u : ℝ) : -2 * Real.pi * u * (-t / (2 * Real.pi)) = t * u := by
    field_simp [Real.pi_ne_zero]
  simp_rw [hphase]
  have hfun :
      (fun u : ℝ => Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) • boxProfile a u) =
      Set.indicator (Set.Ioc (-a) a)
        (fun u : ℝ => Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)) := by
    funext u
    by_cases hu : u ∈ Set.Ioc (-a) a <;> simp [boxProfile, hu]
  rw [hfun, MeasureTheory.integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -a ≤ a)]
  exact box_angular_integral a t

/-- Two genuine compact-supported interval profiles have no common Fourier
zero at any real angular frequency. They are not smooth Weil packets. -/
theorem log23_box_fourier_no_common_zero (t : ℝ) :
    ¬ (𝓕 (boxProfile (Real.log 2)) (-t / (2 * Real.pi)) = 0 ∧
      𝓕 (boxProfile (Real.log 3)) (-t / (2 * Real.pi)) = 0) := by
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have h2c : (Real.log (2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h2
  have h3c : (Real.log (3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h3
  rw [fourier_boxProfile_scaled h2.le, fourier_boxProfile_scaled h3.le]
  rintro ⟨hA, hB⟩
  apply log23_sinc_no_common_zero t
  constructor
  · have hA' := (mul_eq_zero.mp hA).resolve_left (mul_ne_zero (by norm_num) h2c)
    exact_mod_cast hA'
  · have hB' := (mul_eq_zero.mp hB).resolve_left (mul_ne_zero (by norm_num) h3c)
    exact_mod_cast hB'

#print axioms AEGIS.RHBoxFourierComplementarityV1.fourier_boxProfile_scaled
#print axioms AEGIS.RHBoxFourierComplementarityV1.log23_box_fourier_no_common_zero
#print axioms AEGIS.RHBoxFourierComplementarityV1.boxProfile_hasCompactSupport

end AEGIS.RHBoxFourierComplementarityV1
