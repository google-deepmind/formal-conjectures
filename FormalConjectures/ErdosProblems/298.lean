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
# Erdős Problem 298

*Reference:* [erdosproblems.com/298](https://www.erdosproblems.com/298)
-/
/-- Does every set `A ⊆ N` of positive density contain some finite `S ⊂ A` such that
`∑ n ∈ S, 1 / n = 1`?

The answer is yes, proved by Bloom [Bl21].

[Bl21] Bloom, T. F., _On a density conjecture about unit fractions_. arXiv:2112.03726 (2021).

Note: The solution to this problem has been formalized in Lean 3 by T. Bloom and B. Mehta, see
https://github.com/b-mehta/unit-fractions -/
@[category research solved, AMS 11]
theorem erdos_298 : (∀ (A : Set ℕ), 0 ∉ A → A.HasPosDensity →
    ∃ (S : Finset ℕ), S.toSet ⊆ A ∧ ∑ n ∈ S, (1 / n : ℚ) = 1) ↔ answer(True) := by
  sorry

/--
In [Bl21] it is proved under the weaker assumption that `A` only has positive upper density.
-/
@[category research solved, AMS 11]
theorem erdos_298.variants.upper_density : (∀ (A : Set ℕ), 0 < A.upperDensity →
    ∃ (S : Finset ℕ), S.toSet ⊆ A ∧ ∑ n ∈ S, (1 / n : ℚ) = 1) ↔ answer(True) := by
  sorry
