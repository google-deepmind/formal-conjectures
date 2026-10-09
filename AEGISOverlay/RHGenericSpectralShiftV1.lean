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


import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Analysis.MellinTransform

/-!
# Removing common complex zeros by a real spectral shift

The forbidden real shifts of a countable complex zero set form a countable
set. A real shift outside that set gives two functions with no common complex
zero. Every nonzero entire function has a countable zero set, so this applies
to its real spectral shifts. Applying the moment polynomial afterwards leaves
only its two required roots.

The Mellin specialization identifies the shift with multiplication by a real
complex power. Smooth packet membership and function-space approximation are
not asserted.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology

namespace AEGIS.RHGenericSpectralShiftV1

/-- A countable complex zero set admits a real shift with no shared zero. -/
theorem exists_real_shift_no_common_zero (F : ℂ → ℂ)
    (hZ : Set.Countable {z : ℂ | F z = 0}) :
    ∃ a : ℝ, ∀ z : ℂ, ¬ (F z = 0 ∧ F (z + (a : ℂ)) = 0) := by
  let bad : Set ℝ :=
    (fun p : ℂ × ℂ => (p.2 - p.1).re) ''
      ({z : ℂ | F z = 0} ×ˢ {z : ℂ | F z = 0})
  have hbad : bad.Countable := (hZ.prod hZ).image _
  have hex : ∃ a : ℝ, a ∉ bad := by
    by_contra! h
    have heq : bad = Set.univ := Set.eq_univ_of_forall h
    exact Set.not_countable_univ (heq ▸ hbad)
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ?_⟩
  rintro z ⟨hz, hza⟩
  apply ha
  refine ⟨(z, z + (a : ℂ)), ⟨hz, hza⟩, ?_⟩
  simp

/-- A nonzero entire function has at most countably many zeros. -/
theorem countable_zero_set_of_entire (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F Set.univ) (z₀ : ℂ) (hz₀ : F z₀ ≠ 0) :
    Set.Countable {z : ℂ | F z = 0} := by
  have hev : ∀ᶠ z in Filter.codiscreteWithin (Set.univ : Set ℂ), F z ≠ 0 := by
    apply (hF.eqOn_zero_or_eventually_ne_zero_of_preconnected
      isPreconnected_univ).resolve_left
    intro hzero
    exact hz₀ (hzero (Set.mem_univ z₀))
  have hdis : IsDiscrete ({z : ℂ | F z = 0} ∩ Set.univ) :=
    isDiscrete_of_codiscreteWithin (s := {z : ℂ | F z = 0}) hev
  have hc := (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdis
  simpa using hc

/-- The spectral shift construction applies to every nonzero entire function. -/
theorem exists_real_shift_no_common_zero_of_entire (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F Set.univ) (z₀ : ℂ) (hz₀ : F z₀ ≠ 0) :
    ∃ a : ℝ, ∀ z : ℂ, ¬ (F z = 0 ∧ F (z + (a : ℂ)) = 0) :=
  exists_real_shift_no_common_zero F (countable_zero_set_of_entire F hF z₀ hz₀)

/-- Real-power multiplication implements the complementary shift for the
actual Mellin transform. Entirety and a nonzero value are explicit inputs. -/
theorem exists_mellin_power_tilt_no_common_zero (f : ℝ → ℂ)
    (hf : AnalyticOnNhd ℂ (mellin f) Set.univ) (z₀ : ℂ) (hz₀ : mellin f z₀ ≠ 0) :
    ∃ a : ℝ, ∀ z : ℂ,
      ¬ (mellin f z = 0 ∧ mellin (fun x => (x : ℂ) ^ (a : ℂ) • f x) z = 0) := by
  obtain ⟨a, ha⟩ := exists_real_shift_no_common_zero_of_entire (mellin f) hf z₀ hz₀
  refine ⟨a, ?_⟩
  intro z
  rw [mellin_cpow_smul]
  exact ha z

/-- Adding the moment polynomial after the shift creates only the prescribed
common roots 0 and 1. -/
theorem moment_polynomial_common_zeros_exact (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F Set.univ) (z₀ : ℂ) (hz₀ : F z₀ ≠ 0) :
    ∃ a : ℝ, ∀ z : ℂ,
      (z * (z - 1) * F z = 0 ∧ z * (z - 1) * F (z + (a : ℂ)) = 0) ↔
        z = 0 ∨ z = 1 := by
  obtain ⟨a, ha⟩ := exists_real_shift_no_common_zero_of_entire F hF z₀ hz₀
  refine ⟨a, ?_⟩
  intro z
  constructor
  · rintro ⟨h1, h2⟩
    by_contra! h
    have hp : z * (z - 1) ≠ 0 := mul_ne_zero h.1 (sub_ne_zero.mpr h.2)
    exact ha z ⟨(mul_eq_zero.mp h1).resolve_left hp,
      (mul_eq_zero.mp h2).resolve_left hp⟩
  · rintro (rfl | rfl) <;> simp

#print axioms AEGIS.RHGenericSpectralShiftV1.exists_real_shift_no_common_zero_of_entire
#print axioms AEGIS.RHGenericSpectralShiftV1.exists_mellin_power_tilt_no_common_zero
#print axioms AEGIS.RHGenericSpectralShiftV1.moment_polynomial_common_zeros_exact

end AEGIS.RHGenericSpectralShiftV1
