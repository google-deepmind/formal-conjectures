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

import Mathlib
open scoped Topology
open Classical

namespace Erdos668

/-- The number of unit distances among a finite set of points in the plane.
    Each unordered pair at distance 1 contributes 1. -/
noncomputable def UnitDistances (S : Finset (ℝ × ℝ)) : ℕ :=
  ((S ×ˢ S).filter fun ⟨p, q⟩ => dist p q = 1).card / 2

/-- Two finite sets of points are congruent if one can be mapped onto the other
    by a distance‑preserving transformation of the plane. -/
def Congruent (S T : Finset (ℝ × ℝ)) : Prop :=
  ∃ (f : (ℝ × ℝ) → (ℝ × ℝ)), (∀ x y, dist (f x) (f y) = dist x y) ∧ Finset.image f S = T

/-- The number of incongruent sets of n points in ℝ² that maximise the
    number of unit distances tends to infinity as n → ∞. -/
@[category research open, AMS 52C10]
theorem erdos_668.tendsto_infinity :
    ∀ K : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      ∃ (families : Finset (Finset (ℝ × ℝ))),
        (∀ S ∈ families, S.card = n ∧
          (∀ T : Finset (ℝ × ℝ), T.card = n → UnitDistances T ≤ UnitDistances S)) ∧
        families.card = K ∧
        (∀ S ∈ families, ∀ T ∈ families, S ≠ T → ¬ Congruent S T) :=
  sorry

/-- For every n > 3 there exists more than one incongruent set of n points
    that maximises the number of unit distances. -/
@[category research open, AMS 52C10]
theorem erdos_668.always_gt_one :
    ∀ n > 3, ∃ (S T : Finset (ℝ × ℝ)),
      S.card = n ∧ T.card = n ∧
      (∀ U : Finset (ℝ × ℝ), U.card = n → UnitDistances U ≤ UnitDistances S) ∧
      (∀ U : Finset (ℝ × ℝ), U.card = n → UnitDistances U ≤ UnitDistances T) ∧
      ¬ Congruent S T :=
  sorry

end Erdos668
