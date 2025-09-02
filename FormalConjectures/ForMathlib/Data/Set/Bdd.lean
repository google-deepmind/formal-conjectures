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

import Mathlib.Order.Interval.Finset.Defs

variable {β : Type*} [Preorder β]
variable (S : Set β) (a b : β)

/--
Given a set `S` and an element `b` in an order `β`, where all intervals bounded above are finite,
`Set.bdd S b A` is the intersection `S ∩ A ∩ Iio b`.
-/
@[inline]
abbrev Set.interIio (S : Set β) (b : β) : Set β :=
  S ∩ Set.Iio b

/--
Given a set `S` and an element `b` in an order `β` with bottom element `⊥`, where all intervals
bounded above are finite, `Set.bddPos S b A` is the intersection `S ∩ A ∩ Ioc ⊥ b`.
-/
@[inline]
abbrev Set.interIoc [OrderBot β] (S : Set β) (a b : β) : Set β :=
  S ∩ (Set.Ioc a b)

variable {S b} in
theorem Set.finite_interIio [LocallyFiniteOrderBot β] :
    (S.interIio b).Finite :=
  Set.finite_Iio b |>.inter_of_right S

noncomputable instance [LocallyFiniteOrderBot β] : Fintype (S.interIio b) :=
  Set.finite_interIio.fintype

variable {S a b} in
theorem Set.finite_interIoc [LocallyFiniteOrder β] [OrderBot β] :
    (S.interIoc a b).Finite :=
  Set.finite_Ioc a b |>.inter_of_right S

noncomputable instance [LocallyFiniteOrder β] [OrderBot β] : Fintype (S.interIoc a b) :=
  Set.finite_interIoc.fintype

@[simp]
theorem Set.interIio_univ (b : β) : Set.interIio .univ b = Set.Iio b := by
  rw [Set.interIio, univ_inter]

@[simp]
theorem Set.interIio_univ' (b : β) : Set.univ.interIio b = Set.Iio b := by
  rw [Set.interIio_univ]

@[simp]
theorem Set.interIio_empty (b : β) : Set.interIio ∅ b = ∅ := by
  rw [Set.interIio, empty_inter]

theorem Set.interIio_mono {S T : Set β} (h : S ⊆ T) (b : β) : S.interIio b ⊆ T.interIio b :=
  Set.inter_subset_inter_left _ h
