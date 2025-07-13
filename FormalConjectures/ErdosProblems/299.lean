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
# Erdős Problem 299

*Reference:* [erdosproblems.com/299](https://www.erdosproblems.com/299)
-/

open Filter

/--
Is there an infinite sequence $a_1 < a_2 < \dots$ such that $a_{i+1} - a_i = O(1)$ and no finite
sum of $\frac{1}{a_i}$ is equal to 1?
-/
@[category research solved, AMS 11 40]
theorem erdos_299 : (∃ (a : ℕ → ℕ),
    StrictMono a ∧ (∀ n, 0 < a n) ∧
    (fun n ↦ (a (n + 1) : ℝ) - a n) =O[atTop] (1 : ℕ → ℝ) ∧
    ∀ S : Finset ℕ, ∑ i ∈ S, (1 : ℝ) / a i ≠ 1) ↔ answer(False) := by
  sorry

/--
The corresponding question is also false if one replaces sequences such that $a_{i+1} - a_i = O(1)$
with sets of positive density, as follows from [Bl21].

The statement is as follows:
If $A \subset \mathbb{N}$ has positive upper density (and hence certainly if $A$ has positive
density) then there is a finite $S \subset A$ such that $\sum_{n \in S} \frac{1}{n} = 1$.

[Bl21] Bloom, T. F., On a density conjecture about unit fractions.
-/
@[category research solved, AMS 11 40]
theorem erdos_299.variants.density : ∀ (A : Set ℕ), 0 ∉ A → 0 < A.upperDensity →
    ∃ S : Finset ℕ, S.toSet ⊆ A ∧ ∑ n ∈ S, (1 : ℝ) / n = 1 := by
  sorry
