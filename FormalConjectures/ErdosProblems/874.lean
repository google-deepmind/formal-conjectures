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
# Erdős Problem 874

*Reference:* [erdosproblems.com/874](https://www.erdosproblems.com/874)
-/

open Filter Asymptotics Set

namespace Erdos874

/-- The $r$-fold distinct sumset of `A`. -/
def rSumset (A : Set ℕ) (r : ℕ) : Set ℕ :=
  { n | ∃ s : Finset ℕ, ↑s ⊆ A ∧ s.card = r ∧ s.sum id = n }

/-- Finite admissible sets: distinct-order sumsets are pairwise disjoint. -/
def IsAdmissible (A : Set ℕ) : Prop :=
  ∀ r t : ℕ, 1 ≤ r → 1 ≤ t → r ≠ t → Disjoint (rSumset A r) (rSumset A t)

/-- $k(N)$ is the size of the largest admissible subset of $\{1,\ldots,N\}$. -/
noncomputable def k (N : ℕ) : ℕ :=
  sSup { m | ∃ A : Set ℕ, A ⊆ Icc 1 N ∧ IsAdmissible A ∧ A.ncard = m }

/--
Let $k(N)$ denote the size of the largest set $A\subseteq \{1,\ldots,N\}$ such that the sets
$$
S_r = \{ a_1+\cdots +a_r : a_1<\cdots<a_r\in A\}
$$
are disjoint for distinct $r\geq 1$. Estimate $k(N)$ - in particular, is it true that
$k(N)\sim 2N^{1/2}$?
-/
@[category research open, AMS 5 11]
theorem erdos_874 :
    answer(sorry) ↔
      (fun N : ℕ ↦ (k N : ℝ)) =Θ[atTop] fun N ↦ 2 * (N : ℝ) ^ ((1 : ℝ) / 2) := by
  sorry

end Erdos874
