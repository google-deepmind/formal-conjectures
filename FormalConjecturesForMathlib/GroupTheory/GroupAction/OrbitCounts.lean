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
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

/-!
# Numbers of orbits and orbitals

* `MulAction.numOrbits G α`: the number of orbits of `G` on `α`, fixed points included;
* `MulAction.numOrbitals G α`: the number of orbitals, the orbits of `G` on `α × α`; for a
  transitive action this is its rank, the number of orbits of a point stabiliser.
-/

namespace MulAction

variable (G α : Type*) [Group G] [MulAction G α]

/-- The number of orbits of `G` on `α`, fixed points included. -/
noncomputable def numOrbits : ℕ := Nat.card (orbitRel.Quotient G α)

/-- The number of orbits of `G` on `α × α`. -/
noncomputable def numOrbitals : ℕ := Nat.card (orbitRel.Quotient G (α × α))


theorem numOrbits_eq_one [IsPretransitive G α] [Nonempty α] : numOrbits G α = 1 := by
  rw [numOrbits, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Quotient.inductionOn₂ a b fun x y => ?_⟩,
    ⟨Quotient.mk _ (Classical.arbitrary α)⟩⟩
  obtain ⟨g, hg⟩ := exists_smul_eq G y x
  exact Quotient.sound (orbitRel_apply.mpr ⟨g, hg⟩)

end MulAction
