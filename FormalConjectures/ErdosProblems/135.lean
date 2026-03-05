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
# Erdős Problem 135

*Reference:* [erdosproblems.com/135](https://www.erdosproblems.com/135)

Erdős and Gyárfás conjectured that any set of $n$ points in the plane where every
$4$ points determine at least $5$ distinct distances must have $\gg n^2$ total distinct
distances. This was disproved by Tao (2024).

[Er97b] Erdős, P., _Some of my favourite problems which recently have been solved_,
Proceedings of the International Conference on Discrete Mathematics (ICDM) (1997).

[Er97e] Erdős, P., _Some old and new problems in combinatorial geometry_ (1997).

[Ta24c] Tao, T., _A counterexample to the Erdős–Gyárfás conjecture on distances_ (2024).
-/

namespace Erdos135

/-- The number of distinct pairwise distances in a finite point set $A \subseteq \mathbb{R}^2$. -/
noncomputable def numDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (((A ×ˢ A).filter (fun p => p.1 ≠ p.2)).image (fun p => dist p.1 p.2)).card

/-- A finite point set $A \subseteq \mathbb{R}^2$ satisfies the "four-point, five-distance" property
if every $4$-element subset determines at least $5$ distinct pairwise distances. -/
def FourPointFiveDist (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ A → S.card = 4 → 5 ≤ numDistances S

/--
Erdős–Gyárfás Conjecture (Problem 135) [Er97b, Er97e]:
Let $A \subseteq \mathbb{R}^2$ be a set of $n$ points such that any $4$ points determine at least
$5$ distinct distances. Must $A$ determine $\gg n^2$ many distances?

The conjecture asserts YES: there exists an absolute constant $c > 0$ such that
every finite $A \subseteq \mathbb{R}^2$ with the four-point-five-distance property satisfies
$|\text{distinct distances of } A| \geq c \cdot n^2$.

This was answered in the NEGATIVE by Tao [Ta24c], who constructed for any
large $n$ a set of $n$ points where any $4$ points determine at least $5$ distinct
distances, yet the number of distinct distances is $O(n^2 / \sqrt{\log n})$.
-/
@[category research solved, AMS 5 52]
theorem erdos_135 :
    answer(False) ↔
      ∃ c : ℝ, 0 < c ∧
        ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
          FourPointFiveDist A →
          c * (A.card : ℝ) ^ 2 ≤ (numDistances A : ℝ) := by
  sorry

end Erdos135
