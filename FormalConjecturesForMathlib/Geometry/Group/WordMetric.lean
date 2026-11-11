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

public import Mathlib.Analysis.Normed.Group.Defs
public import FormalConjecturesForMathlib.Geometry.Group.WordProd

/-!
# The word metric

The word length of an element is the length of a shortest representing word, over a generating
family given by `Group.Generators`. The word length defines a norm on `G` inducing the word metric
`dist g h = ‖g⁻¹ * h‖`.

This file is copied from `Mathlib.Geometry.Group.WordMetric`
(leanprover-community/mathlib4#43118). It is in Mathlib from `v4.34.0`.

TODO: delete this file when this repository moves to Mathlib `v4.34.0`.

## Main definitions

* `Group.Generators.wordLength`: the word length of an element of `G` with respect to a
  generating family `P`.
* `Group.Generators.IsGeodesic`: a word is geodesic if it is of minimal length among the words
  representing the same group element.
* `Group.Generators.groupNorm`: the word length as a norm on `G`.
* `Group.Generators.normedGroup`: the normed group structure on `G` induced by `groupNorm`.
  This gives rise to a word metric on `G`.

## Main results

* `Group.Generators.exists_isGeodesic`: every element of `G` is represented by some geodesic
  word.
-/

@[expose] public section

namespace Group.Generators

variable {G ι : Type*} [Group G]

variable (P : Group.Generators G ι) (g h : G) (l : List (ι × Bool))

/-! ### Definition of word length -/

/-- The word length of `g` with respect to the generating family `P`. -/
@[no_expose]
noncomputable def wordLength : ℕ := sInf {n | ∃ l, P.wordProd l = g ∧ l.length = n}

/-! ### Geodesic words -/

/-- A word `l` is geodesic if its length is exactly the word length of the group element it
represents. -/
def IsGeodesic : Prop := P.wordLength (P.wordProd l) = l.length

lemma IsGeodesic.eq {l : List (ι × Bool)} (hl : P.IsGeodesic l) :
    P.wordLength (P.wordProd l) = l.length := hl

/-- Every group element has a geodesic word representative. -/
theorem exists_isGeodesic : ∃ l, P.IsGeodesic l ∧ P.wordProd l = g := by
  obtain ⟨l, rfl, hlen⟩ := Nat.sInf_mem (Set.Nonempty.image List.length (P.wordProd_surjective g))
  exact ⟨l, hlen.symm, rfl⟩

/-! ### Word length -/

lemma wordLength_wordProd_le : P.wordLength (P.wordProd l) ≤ l.length :=
  Nat.sInf_le ⟨l, rfl, rfl⟩

/-- The characterisation of word length: the word length of a group element is less or equal to `n`
if and only if there exists a word `l` of length at most `n` which evaluates to `g`. -/
theorem wordLength_le_iff {n : ℕ} : P.wordLength g ≤ n ↔ ∃ l, l.length ≤ n ∧ P.wordProd l = g := by
  constructor
  · intro h
    obtain ⟨l, hl, rfl⟩ := P.exists_isGeodesic g
    exact ⟨l, hl.eq ▸ h, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact (P.wordLength_wordProd_le l).trans hl

variable {g} in
@[simp]
lemma wordLength_eq_zero_iff : P.wordLength g = 0 ↔ g = 1 := by
  rw [← Nat.le_zero, wordLength_le_iff]
  simp [eq_comm]

@[simp]
lemma wordLength_one : P.wordLength (1 : G) = 0 := by
  rw [wordLength_eq_zero_iff]

-- This is superseded by `wordLength_inv`.
private lemma wordLength_inv_le : P.wordLength g⁻¹ ≤ P.wordLength g := by
  obtain ⟨l, hl, rfl⟩ := P.exists_isGeodesic g
  simpa [wordProd_invRev, hl.eq] using P.wordLength_wordProd_le (FreeGroup.invRev l)

@[simp]
lemma wordLength_inv : P.wordLength g⁻¹ = P.wordLength g := by
  apply le_antisymm
  · exact P.wordLength_inv_le g
  · simpa using P.wordLength_inv_le g⁻¹

lemma wordLength_mul_le : P.wordLength (g * h) ≤ P.wordLength g + P.wordLength h := by
  obtain ⟨l₁, hl₁, rfl⟩ := P.exists_isGeodesic g
  obtain ⟨l₂, hl₂, rfl⟩ := P.exists_isGeodesic h
  simpa [wordProd_append, hl₁.eq, hl₂.eq] using P.wordLength_wordProd_le (l₁ ++ l₂)

/-- The `wordLength` with respect to a generating family `P` defines a norm on `G`. -/
noncomputable def groupNorm : GroupNorm G where
  toFun g := P.wordLength g
  map_one' := by simp
  mul_le' := mod_cast P.wordLength_mul_le
  inv' := by simp
  eq_one_of_map_eq_zero' := by simp

/-! ### Word metric -/

/-- `G` as a metric space `NormedGroup G` with respect to a generating family `P`. The metric is
given by `dist g h = ‖g⁻¹ * h‖`, where the norm is given by `groupNorm`. -/
@[instance_reducible]
noncomputable def normedGroup : NormedGroup G := P.groupNorm.toNormedGroup

end Group.Generators
