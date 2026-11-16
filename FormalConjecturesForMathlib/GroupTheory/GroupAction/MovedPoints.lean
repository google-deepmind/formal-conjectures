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

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Moved points and the minimal degree

* `MulAction.movedPoints G α`: the points of `α` moved by some element of `G`;
* `MulAction.numMovedPoints G α`: their number, the degree of a permutation group;
* `MulAction.minimalDegree G α`: the least number of points moved by an element that moves one.
-/

namespace MulAction

variable (G α : Type*) [Group G] [MulAction G α]

/-- The points moved by some element of `G`. -/
def movedPoints : Set α := {a : α | ∃ g : G, g • a ≠ a}

/-- The number of points moved by some element of `G`. -/
noncomputable def numMovedPoints : ℕ := (movedPoints G α).ncard

/-- The least number of points moved by an element that moves some point (`0` if no element
moves a point). -/
noncomputable def minimalDegree : ℕ :=
  sInf {k : ℕ | ∃ g : G, (fixedBy α g)ᶜ.Nonempty ∧ (fixedBy α g)ᶜ.ncard = k}


@[simp]
theorem movedPoints_of_subsingleton [Subsingleton G] : movedPoints G α = ∅ := by
  ext a
  simp [movedPoints, Subsingleton.elim _ (1 : G)]

@[simp]
theorem numMovedPoints_of_subsingleton [Subsingleton G] : numMovedPoints G α = 0 := by
  simp [numMovedPoints]

end MulAction
