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

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Order.Filter.AtTopBot.Defs

variable {M : Type*} [AddCommMonoid M]

open scoped List

/-- The set of subset sums of a set `A ⊆ M`. -/
def subsetSums (A : Set M) : Set M :=
  {n | ∃ B : Finset M, B.toSet ⊆ A ∧ n = ∑ i ∈ B, i}

/-- The set of subset sums of a sequence `ℕ → M`. -/
def subseqSums (A : ℕ → M) : Set M :=
  {n | ∃ B : Finset ℕ, B.toSet.InjOn A ∧ n = ∑ i ∈ B, A i}

/-- The set of subset sums of a sequence `ℕ → M`, where repetition is allowed. -/
def subseqSums' (A : ℕ → M) : Set M :=
  {n | ∃ B : Finset ℕ, n = ∑ i ∈ B, A i}

/-- A set `A ⊆ M` is complete if every sufficiently large element of `M` is a subset sum of `A`. -/
def IsAddComplete [Preorder M] (A : Set M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subsetSums A

/-- A sequence `A` is complete if every sufficiently large element of `M` is a sum of
distinct terms of `A`. -/
def IsAddCompleteNatSeq [Preorder M] (A : ℕ → M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subseqSums A

/-- A sequence `A` is complete if every sufficiently large element of `M` is a sum of
(not necessarily distinct) terms of `A`. -/
def IsAddCompleteNatSeq' [Preorder M] (A : ℕ → M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subseqSums' A
