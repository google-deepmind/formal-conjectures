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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 782

*Reference:* [erdosproblems.com/782](https://www.erdosproblems.com/782)

A question of Brown, Erdős, and Freedman [BEF90]. It is a classical fact that
the squares do not contain arithmetic progressions of length 4. An affirmative
answer to the first question implies an affirmative answer to the second.

[BEF90] Brown, T. C., Erdős, P., and Freedman, A. R., _Quasi-progressions and
descending waves_. J. Combin. Theory Ser. A 53 (1990), no. 1, 81-95.
-/

open Finset

open scoped BigOperators

namespace Erdos782

/--
Erdős Problem 782, Part 1 (Quasi-progressions in the squares) [BEF90]:

There exists a constant $C$ such that for any $k \geq 2$, one can find $k$ perfect
squares $x_1 < x_2 < \cdots < x_k$ forming a quasi-progression with gap $d$, meaning
$x_i + d \leq x_{i+1} \leq x_i + d + C$ for all consecutive pairs.
-/
@[category research open, AMS 5 11]
theorem erdos_782 : answer(sorry) ↔
    ∃ C : ℕ, ∀ k : ℕ, k ≥ 2 →
    ∃ (x : Fin k → ℕ) (d : ℕ), d > 0 ∧
    (∀ i, IsSquare (x i)) ∧
    (∀ i j : Fin k, i < j → x i < x j) ∧
    (∀ (i : ℕ) (hi : i + 1 < k),
      x ⟨i, by omega⟩ + d ≤ x ⟨i + 1, hi⟩ ∧
      x ⟨i + 1, hi⟩ ≤ x ⟨i, by omega⟩ + d + C) := by
  sorry

/--
Erdős Problem 782, Part 2 (Combinatorial cubes in the squares) [BEF90]:

For any $m$, the set of perfect squares contains a combinatorial cube of
dimension $m$: there exist $a$ and positive $b_1, \ldots, b_m$ such that
$a + \sum_{i \in S} b_i$ is a perfect square for every subset
$S \subseteq \{1, \ldots, m\}$.
-/
@[category research open, AMS 5 11]
theorem erdos_782.variants.cubes : answer(sorry) ↔
    ∀ m : ℕ, ∃ (a : ℕ) (b : Fin m → ℕ),
    (∀ i, b i > 0) ∧
    (∀ S : Finset (Fin m), IsSquare (a + ∑ i ∈ S, b i)) := by
  sorry

end Erdos782
