/-
Copyright 2025 The Formal Conjectures Authors.

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

import Mathlib.Analysis.SpecificLimits.Basic
import FormalConjectures.ForMathlib.Algebra.Order.Group.Pointwise.Interval
import FormalConjectures.ForMathlib.Order.Interval.Finset.Basic
import FormalConjectures.ForMathlib.Order.Interval.Finset.Nat

variable {β : Type*} [Preorder β] --[LocallyFiniteOrderBot β]
variable (S : Set β) (b : β) (A : Set β := .univ)

/--
Given a set `S` and an element `b` in an order `β`, where all intervals bounded above are finite,
we define the partial density of `S` (relative to a set `A`) to be the proportion of elements in
`{x ∈ A | x < b}` that lie in `S ∩ A`.

This definition was inspired from https://github.com/b-mehta/unit-fractions
-/
@[inline]
noncomputable abbrev Set.bdd (S : Set β) (b : β) (A : Set β := .univ) : Set β :=
  S ∩ A ∩ Set.Iio b

@[inline]
noncomputable abbrev Set.bddPos [OrderBot β] (S : Set β) (b : β) (A : Set β := .univ) : Set β :=
  S ∩ A ∩ (Set.Ioc ⊥ b)

theorem Set.finite_bdd [LocallyFiniteOrderBot β] (S : Set β) (b : β) (A : Set β := .univ) :
    (S.bdd b A).Finite :=
  Set.finite_Iio b |>.inter_of_right (S ∩ A)

noncomputable instance [LocallyFiniteOrderBot β] : Fintype (S.bdd b A) :=
  Set.finite_bdd S b A |>.fintype

theorem Set.finite_bddPos [LocallyFiniteOrder β] [OrderBot β] (S : Set β) (b : β) (A : Set β := .univ) :
    (S.bddPos b A).Finite :=
  Set.finite_Ioc ⊥ b |>.inter_of_right (S ∩ A)

noncomputable instance [LocallyFiniteOrder β] [OrderBot β] : Fintype (S.bddPos b A) :=
  Set.finite_bddPos S b A |>.fintype

@[simp]
theorem Set.bdd_univ (b : β) (A : Set β) : Set.bdd .univ b A = A ∩ Set.Iio b := by
  rw [Set.bdd, univ_inter]

@[simp]
theorem Set.bdd_univ' (b : β) : Set.univ.bdd b = Set.Iio b := by
  rw [Set.bdd_univ, univ_inter]

@[simp]
theorem Set.bdd_empty (b : β) (A : Set β) : Set.bdd ∅ b A = ∅ := by
  rw [Set.bdd, empty_inter, empty_inter]

theorem Set.bdd_mono {S T : Set β} (h : S ⊆ T) (b : β) (A : Set β := .univ) :
    S.bdd b A ⊆ T.bdd b A :=
  Set.inter_subset_inter_left _ (Set.inter_subset_inter_left _ h)
