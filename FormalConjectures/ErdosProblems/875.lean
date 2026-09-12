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

import FormalConjecturesUtil

/-!
# Erdős Problem 875

*References:*
- [erdosproblems.com/875](https://www.erdosproblems.com/875)
- [Er98] Erdős, Paul, Some of my new and almost new problems and results in combinatorial number
  theory. Number theory (Eger, 1996) (1998), 169-180.
-/

open Filter

open scoped Topology

namespace Erdos875

/-- The set of sums of `r` distinct elements of `A`. This is $S_r$ in the problem statement. -/
def rSumset (A : Set ℕ) (r : ℕ) : Set ℕ :=
  {n | ∃ s : Finset ℕ, ↑s ⊆ A ∧ s.card = r ∧ s.sum id = n}

/-- An admissible set: the sumsets $S_r$ of distinct `r`-fold sums are pairwise disjoint
for $r \geq 1$. -/
def IsAdmissible (A : Set ℕ) : Prop :=
  ∀ r t : ℕ, 1 ≤ r → 1 ≤ t → r ≠ t → Disjoint (rSumset A r) (rSumset A t)

/-- The increasing enumeration of `A`. If `A` is infinite, `a A n` is the $(n+1)$-st element. -/
noncomputable def a (A : Set ℕ) (n : ℕ) : ℕ := Nat.nth (· ∈ A) n

/--
Let $A=\{a_1<a_2<\cdots\}\subset \mathbb{N}$ be an infinite set such that the sets
$$S_r = \{ a_1+\cdots +a_r : a_1<\cdots<a_r\in A\}$$
are disjoint for distinct $r\geq 1$. How fast can such a sequence grow? How small can
$a_{n+1}-a_n$ be? In particular, for which $c$ is it possible that $a_{n+1}-a_n\leq n^{c}$?

A problem of Deshouillers and Erdős (an infinite version of [874](https://www.erdosproblems.com/874)).
Such sets are sometimes called admissible. Erdős writes 'it [is not] completely trivial to find
such a sequence for which $a_{n+1}/a_n\to 1$'. It is not clear from this whether Deshouillers
and Erdős knew of such a sequence.
-/
@[category research open, AMS 5]
theorem erdos_875 :
    answer(sorry) = {c : ℝ | ∃ A : Set ℕ, A.Infinite ∧ IsAdmissible A ∧
      ∀ᶠ n : ℕ in atTop, (a A (n + 1) : ℝ) - a A n ≤ (n : ℝ) ^ c} := by
  sorry

/--
Erdős writes 'it [is not] completely trivial to find such a sequence for which
$a_{n+1}/a_n\to 1$'. It is not clear from this whether Deshouillers and Erdős knew of such a
sequence.
-/
@[category research open, AMS 5]
theorem erdos_875.variants.ratio_limit :
    answer(sorry) ↔ ∃ A : Set ℕ, A.Infinite ∧ IsAdmissible A ∧
      Tendsto (fun n => (a A (n + 1) : ℝ) / a A n) atTop (𝓝 1) := by
  sorry

end Erdos875
