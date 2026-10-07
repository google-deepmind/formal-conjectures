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

import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Subexponential growth is invariant under bounded perturbations

For complex-valued functions on the positive real half-line, use the direct
majorant form of exponential type zero. If two functions differ by a uniform
bounded amount for t >= 0, then either one is subexponential iff the other is.

This is the exact transport needed to discard bounded arithmetic and
Archimedean correction layers without changing the RH growth target.

AUTHORITY_EFFECT = NONE.
RH_PROVEN_UNCONDITIONALLY = false.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHSubexpBoundedPerturbationV1

def SubexponentialAtTopV1 (F : ℝ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖F t‖ ≤ C * Real.exp (ε * t)

def BoundedDifferenceOnNonnegativeV1 (F G : ℝ → ℂ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 0 ≤ t → ‖F t - G t‖ ≤ D

theorem subexponential_of_bounded_difference_v1
    (F G : ℝ → ℂ)
    (hG : SubexponentialAtTopV1 G)
    (hFG : BoundedDifferenceOnNonnegativeV1 F G) :
    SubexponentialAtTopV1 F := by
  obtain ⟨D, hD0, hD⟩ := hFG
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := hG ε hε
  refine ⟨C + D, add_nonneg hC0 hD0, ?_⟩
  intro t ht
  have hE : 1 ≤ Real.exp (ε * t) :=
    Real.one_le_exp (mul_nonneg hε.le ht)
  have hDE : D ≤ D * Real.exp (ε * t) := by
    simpa using mul_le_mul_of_nonneg_left hE hD0
  calc
    ‖F t‖
        ≤ ‖F t - G t‖ + ‖G t‖ := by
          simpa only [sub_add_cancel] using norm_add_le (F t - G t) (G t)
    _ ≤ D + C * Real.exp (ε * t) :=
      add_le_add (hD t ht) (hC t ht)
    _ ≤ D * Real.exp (ε * t) + C * Real.exp (ε * t) := by
      linarith [hDE]
    _ = (C + D) * Real.exp (ε * t) := by ring

theorem boundedDifference_symm_v1
    (F G : ℝ → ℂ)
    (hFG : BoundedDifferenceOnNonnegativeV1 F G) :
    BoundedDifferenceOnNonnegativeV1 G F := by
  obtain ⟨D, hD0, hD⟩ := hFG
  refine ⟨D, hD0, ?_⟩
  intro t ht
  simpa [norm_sub_rev] using hD t ht

theorem subexponential_iff_of_bounded_difference_v1
    (F G : ℝ → ℂ)
    (hFG : BoundedDifferenceOnNonnegativeV1 F G) :
    SubexponentialAtTopV1 F ↔ SubexponentialAtTopV1 G := by
  constructor
  · intro hF
    exact subexponential_of_bounded_difference_v1 G F hF
      (boundedDifference_symm_v1 F G hFG)
  · intro hG
    exact subexponential_of_bounded_difference_v1 F G hG hFG

#print axioms AEGIS.RHSubexpBoundedPerturbationV1.subexponential_of_bounded_difference_v1
#print axioms AEGIS.RHSubexpBoundedPerturbationV1.subexponential_iff_of_bounded_difference_v1

end AEGIS.RHSubexpBoundedPerturbationV1
