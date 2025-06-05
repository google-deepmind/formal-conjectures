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
Is there an infinite sequence $a_1 < a_2 < \dots$ such that $a_{i+1} - a_i = O(1)$ and no finite sum of $\frac{1}{a_i}$ is equal to 1? -/
@[category research solved, AMS 11, AMS 40]
theorem erdos_299 : ∃ (a : ℕ → ℕ), StrictMono a ∧ (∀ n, 0 < a n) ∧
    (fun n ↦ (a (n + 1) : ℝ) - a n) =O[atTop] (fun n ↦ (1 : ℝ)) ∧
    ∀ (S : Finset ℕ), ∑ i ∈ S, (1 : ℝ) / (a i) ≠ 1 := by
  sorry


/--
The following stronger version was proven by T. Bloom:

If $A \subset \mathbb{N}$ has positive upper density (and hence certainly if $A$ has positive density) then there is a finite $S \subset A$ such that $\sum_{n \in S} \frac{1}{n} = 1$.
-/
-- TODO: UPPER DENSITY, and also in 298!
@[category research solved, AMS 11, AMS 40]
theorem erdos_299.variants.density : ∀ (A : Set ℕ), 0 ∉ A → A.HasPosDensity →
    ∃ (S : Finset ℕ), S.toSet ⊆ A ∧ ∑ n ∈ S, (1 : ℝ) / n = 1 := by
  sorry
