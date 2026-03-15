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
# Erdős Problem 654

*Reference:* [erdosproblems.com/654](https://www.erdosproblems.com/654)

Let $f(n)$ be such that, given any $x_1, \ldots, x_n \in \mathbb{R}^2$ with no four points on a
circle, there exists some $x_i$ with at least $f(n)$ many distinct distances to other $x_j$.
Is it true that $f(n) > (1/3 + c)n$ for some $c > 0$, for all large $n$?

The trivial bound is $f(n) \geq (n-1)/3$. The stronger conjecture $f(n) > (1-o(1))n$
was disproved by Aletheia [Fe26].

A problem of Erdős and Pach [Er87b][ErPa90][Er97e].

[Er87b] Erdős, P., _Some combinatorial and metric problems in geometry_. Intuitive geometry
(Siófok, 1985) (1987), 167-177.

[ErPa90] Erdős, P. and Pach, J., _Variations on the theme of repeated distances_,
Combinatorica (1990), 261-269.

[Er97e] Erdős, P., _Some of my favourite problems which recently have been solved_,
Proc. Int. Conf. on Discrete Math. (1997), 527-537.

[Fe26] Feng, T. et al., _Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on
the Erdős Problems_. arXiv:2601.22401 (2026).
-/

open Finset Classical EuclideanGeometry

open scoped EuclideanGeometry

namespace Erdos654

/-- A configuration of $n$ points in $\mathbb{R}^2$ has no four concyclic points
    if no four distinct points lie on a common circle. -/
def NoFourConcyclic (n : ℕ) (pts : Fin n → ℝ²) : Prop :=
  ∀ (i₁ i₂ i₃ i₄ : Fin n),
    i₁ ≠ i₂ → i₁ ≠ i₃ → i₁ ≠ i₄ → i₂ ≠ i₃ → i₂ ≠ i₄ → i₃ ≠ i₄ →
    ¬Concyclic ({pts i₁, pts i₂, pts i₃, pts i₄} : Set ℝ²)

/-- The number of distinct distances from point $i$ to all other points in the
    configuration. -/
noncomputable def numDistinctDistances (n : ℕ) (pts : Fin n → ℝ²) (i : Fin n) : ℕ :=
  ((univ.filter (· ≠ i)).image (fun j => dist (pts i) (pts j))).card

/--
Erdős Problem 654 [Er87b][ErPa90][Er97e]:

There exists a constant $c > 0$ such that for all sufficiently large $n$,
given any $n$ points in $\mathbb{R}^2$ with no four on a circle, there exists some
point with at least $(1/3 + c) \cdot n$ distinct distances to the other points.
-/
@[category research open, AMS 5 52]
theorem erdos_654 : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ pts : Fin n → ℝ², Function.Injective pts →
        NoFourConcyclic n pts →
        ∃ i : Fin n, (numDistinctDistances n pts i : ℝ) > (1 / 3 + c) * ↑n := by
  sorry

end Erdos654
