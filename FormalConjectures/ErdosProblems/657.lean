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
# Erdős Problem 657

*Reference:* [erdosproblems.com/657](https://www.erdosproblems.com/657)

Is it true that if $A \subseteq \mathbb{R}^2$ is a set of $n$ points with no isosceles triangles
(every $3$-point subset determines $3$ distinct distances), then $A$ must determine at least
$f(n) \cdot n$ distinct distances for some $f(n) \to \infty$?

- [Er73] Erdős, P., *Problems and results on combinatorial number theory*.
- [Er75f] Erdős, P., *Problems and results in combinatorial geometry*.
- [ErPa90] Erdős, P. and Pach, J., *Variations on the theme of repeated distances*.
- [Er97e] Erdős, P., *Some of my favourite problems which recently have been solved*.
-/

namespace Erdos657

/-- The number of distinct pairwise distances in a finite point set $A \subseteq \mathbb{R}^2$. -/
noncomputable def numDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (((A ×ˢ A).filter (fun p => p.1 ≠ p.2)).image (fun p => dist p.1 p.2)).card

/-- A finite point set $A \subseteq \mathbb{R}^2$ has no isosceles triangles if every $3$-element
subset determines $3$ distinct pairwise distances. -/
def NoIsoscelesTriangles (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ A → S.card = 3 → numDistances S = 3

/--
**Erdős Problem 657** [Er73, Er75f, ErPa90, Er97e]:

Is it true that if $A \subseteq \mathbb{R}^2$ is a set of $n$ points such that every $3$-point
subset determines $3$ distinct distances (no isosceles triangles), then the number of distinct
distances determined by $A$ is at least $f(n) \cdot n$ for some $f(n) \to \infty$?

Equivalently: for every constant $C > 0$, there exists $N_0$ such that every set of $n \geq N_0$
points in $\mathbb{R}^2$ with no isosceles triangles determines at least $C \cdot n$ distinct
distances.
-/
@[category research open, AMS 5 52]
theorem erdos_657 : answer(sorry) ↔
    ∀ C : ℝ, 0 < C →
      ∃ N₀ : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
        NoIsoscelesTriangles A →
        N₀ ≤ A.card →
        C * (A.card : ℝ) ≤ (numDistances A : ℝ) := by
  sorry

end Erdos657
