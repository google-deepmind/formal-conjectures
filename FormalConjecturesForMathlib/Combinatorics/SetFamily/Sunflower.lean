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

@[expose] public section

/-!
# Sunflowers

This file defines sunflowers of set families.
-/

variable {α : Type*}

/--
A sunflower `F` with kernel `S` is a collection of sets in which all possible distinct pairs of sets
share the same intersection `S`.
-/
def IsSunflowerWithKernel (F : Set (Set α)) (S : Set α) : Prop :=
  F.Pairwise (fun A B => A ∩ B = S)

theorem isSunflowerWithKernel_empty (S : Set α) : IsSunflowerWithKernel {} S := by
  simp [IsSunflowerWithKernel]

theorem isSunflowerWithKernel_singleton (S : Set α) (A : Set α) :
    IsSunflowerWithKernel {A} S := by
  simp [IsSunflowerWithKernel]

/--
A sunflower `F` is a collection of sets in which all possible distinct pairs of sets share the
same intersection.
-/
def IsSunflower (F : Set (Set α)) : Prop := ∃ S, IsSunflowerWithKernel F S

theorem isSunflower_empty : IsSunflower (∅ : Set (Set α)) := by
  simp [IsSunflower, isSunflowerWithKernel_empty]

theorem isSunflower_singleton (A : Set α) : IsSunflower {A} := by
  simp [IsSunflower, isSunflowerWithKernel_singleton]
