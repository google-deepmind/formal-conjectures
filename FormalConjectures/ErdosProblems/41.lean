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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 41

*Reference:* [erdosproblems.com/41](https://www.erdosproblems.com/41)
-/
/--
Let A ⊆ ℕ be an infinite set such that the triple sums a + b + c are all distinct for a, b, c ∈ A (aside from the trivial coincidences). Is it true that lim inf n → ∞ |A ∩ {1, …, N}| / N^(1/3) = 0 ?
-/

def PairCondition (A : Set α) : Prop := ∀ᵉ (I : Finset α) (J : Finset α),
    I.toSet ⊆ A ∧ J.toSet ⊆ A ∧ I.card = 2 ∧ J.card = 2 ∧
    (∑ i ∈ I, i = ∑ j ∈ J, j) → I = J


def TripleCondition (A : Set α) : Prop := ∀ᵉ (I : Finset α) (J : Finset α),
    I.toSet ⊆ A ∧ J.toSet ⊆ A ∧ I.card = 3 ∧ J.card = 3 ∧
    (∑ i ∈ I, i = ∑ j ∈ J, j) → I = J

@[category research open, AMS 11]
theorem erdos_41 : (∀ A : Set ℕ), TripleCondition A ∧ A.Infinite → Filter.atTop.liminf (fun N => (A.bdd N).card / (N : ℝ)^(1/3)) = 0 := by
sorry

@[category research solved, AMS 11]
theorem erdos_41_i : (∀ A : Set ℕ), PairCondition A ∧ A.Infinite → Filter.atTop.liminf (fun N => (A.bdd N).card / (N : ℝ).sqrt) = 0 := by
sorry
