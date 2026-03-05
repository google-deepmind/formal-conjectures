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
-/

open Finset Classical

namespace Erdos654

/-- Squared Euclidean distance between two points in $\mathbb{R}^2$. -/
noncomputable def sqEuclideanDist (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Four points in $\mathbb{R}^2$ are concyclic if they all lie on a common circle
    (with positive radius). Expressed using squared distances. -/
def FourConcyclic (p₁ p₂ p₃ p₄ : ℝ × ℝ) : Prop :=
  ∃ (c : ℝ × ℝ) (r_sq : ℝ), r_sq > 0 ∧
    sqEuclideanDist p₁ c = r_sq ∧ sqEuclideanDist p₂ c = r_sq ∧
    sqEuclideanDist p₃ c = r_sq ∧ sqEuclideanDist p₄ c = r_sq

/-- A configuration of $n$ points in $\mathbb{R}^2$ has no four concyclic points
    if no four distinct points lie on a common circle. -/
def NoFourConcyclic (n : ℕ) (pts : Fin n → ℝ × ℝ) : Prop :=
  ∀ (i₁ i₂ i₃ i₄ : Fin n),
    i₁ ≠ i₂ → i₁ ≠ i₃ → i₁ ≠ i₄ → i₂ ≠ i₃ → i₂ ≠ i₄ → i₃ ≠ i₄ →
    ¬FourConcyclic (pts i₁) (pts i₂) (pts i₃) (pts i₄)

/-- The number of distinct distances from point $i$ to all other points in the
    configuration. Uses squared distances since $d(p,q) = d(p',q')$ iff
    $d(p,q)^2 = d(p',q')^2$ for nonnegative distances. -/
noncomputable def numDistinctDistances (n : ℕ) (pts : Fin n → ℝ × ℝ) (i : Fin n) : ℕ :=
  ((univ.filter (· ≠ i)).image (fun j => sqEuclideanDist (pts i) (pts j))).card

/--
Erdős Problem 654 [Er87b][ErPa90][Er97e]:

There exists a constant $c > 0$ such that for all sufficiently large $n$,
given any $n$ points in $\mathbb{R}^2$ with no four on a circle, there exists some
point with at least $(1/3 + c) \cdot n$ distinct distances to the other points.
-/
@[category research open, AMS 5 52]
theorem erdos_654 : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ pts : Fin n → ℝ × ℝ, Function.Injective pts →
        NoFourConcyclic n pts →
        ∃ i : Fin n, (numDistinctDistances n pts i : ℝ) > (1 / 3 + c) * ↑n := by
  sorry

end Erdos654
