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
# Erdős Problem 817

*Reference:* [erdosproblems.com/817](https://www.erdosproblems.com/817)
-/

open Filter

namespace Erdos817

/-- Define $g_k(n)$ to be the minimal $N$ such that $\{1, ..., N\}$ contains some $A$ of
size $|A| = n$ such that
$$
  \langle A\rangle = \left\{\sum_{a \in A} \epsilon_a a : \epsilon_a \in\{0, 1\}\right\}
$$
contains no non-trivial $k$-term arithmetic progression. -/
noncomputable
def g (k : ℕ) (n : ℕ) : ℕ := sInf { N | ∃ A ⊆ Finset.Icc 1 N, A.card = n ∧
    ∀ s, s ⊆ { ∑ a ∈ B, a | B ∈ A.powerset } → s.IsAPOfLengthFree k}

/-- Let $k\geq 3$. Define $g_k(n)$ to be the minimal $N$ such that
$\{1, ..., N\}$ contains some $A$ of size $|A| = n$ such that
$$
  \langle A\rangle = \left\{\sum_{a \in A} \epsilon_a a : \epsilon_a \in\{0, 1\}\right\}
$$
contains no non-trivial $k$-term arithmetic progression. Estimate $g_k(n)$. In
particular, is it true that
$$
  g_3(n) \gg 3^n
$$ -/
-- Formalisation note : only formalising the "In particular" part
@[category research open, AMS 5 11]
theorem erdos_817 :
    ((fun n => (3 ^ n : ℝ)) =O[atTop] fun n => (g 3 n : ℝ)) ↔ answer(sorry) := by
  sorry

/-- A problem of Erdős and Sárközy who proved
$$
  g_3(n) \gg \frac{3^n}{n^{O(1)}}.
$$ -/
@[category research solved, AMS 5 11]
theorem erdos_817.variants.bdd_power : ∃ O > (0 : ℝ),
    (fun (n : ℕ) => (3 ^ n : ℝ) / n ^ O) =O[atTop] fun n => (g 3 n : ℝ) := by
  sorry

end Erdos817
