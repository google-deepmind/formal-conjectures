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
/- Original Mathlib author: Hang Lu Su. -/
module

public import Mathlib.GroupTheory.Generators

/-!
# Evaluation of words

A generating family `P : Group.Generators G ι` indexed by `ι` gives rise to an evaluation map
`P.wordProd : List (ι × Bool) → G`.

This file is copied from `Mathlib.Geometry.Group.WordProd`
(leanprover-community/mathlib4#43118). It is in Mathlib from `v4.34.0`.

TODO: delete this file when this repository moves to Mathlib `v4.34.0`.

## Main definitions

* `Group.Generators.wordProd`: the canonical map from a word `List (ι × Bool)` over a generating
  family `ι` to the corresponding group `G`. It sends each `(i, true)` to `P.val i` and
  `(i, false)` to `(P.val i)⁻¹`.
-/

@[expose] public section

variable {G ι : Type*} [Group G]

namespace Group.Generators

variable (P : Group.Generators G ι) (i : ι) (b : Bool) (l l₁ l₂ : List (ι × Bool))

/-- The canonical map from a word `List (ι × Bool)` over a generating family `ι` to its
corresponding group `G`. -/
def wordProd : G := FreeGroup.lift P.val (FreeGroup.mk l)

/-- Every element of `G` is the product of some word over a generating family. -/
theorem wordProd_surjective : Function.Surjective P.wordProd :=
  P.lift_val_surjective.comp Quot.mk_surjective

@[simp]
lemma wordProd_nil : P.wordProd [] = 1 := by
  simp [wordProd]

@[simp]
lemma wordProd_singleton : P.wordProd [(i, b)] = cond b (P.val i) (P.val i)⁻¹ := by
  simp [wordProd]

lemma wordProd_cons : P.wordProd ((i, b) :: l) = cond b (P.val i) (P.val i)⁻¹ * P.wordProd l := by
  simp [wordProd]

lemma wordProd_append : P.wordProd (l₁ ++ l₂) = P.wordProd l₁ * P.wordProd l₂ := by
  simp [wordProd]

lemma wordProd_invRev : P.wordProd (FreeGroup.invRev l) = (P.wordProd l)⁻¹ := by
  simp [wordProd, ← FreeGroup.inv_mk]

end Group.Generators
