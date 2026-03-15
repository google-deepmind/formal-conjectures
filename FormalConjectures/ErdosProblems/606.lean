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
import FormalConjecturesForMathlib.Geometry.«2d»

open scoped EuclideanGeometry

/-!
# Erdős Problem 606

*Reference:* [erdosproblems.com/606](https://www.erdosproblems.com/606)

Given any $n$ distinct points in $\mathbb{R}^2$, let $f(n)$ count the number of distinct
lines determined by these points. What are the possible values of $f(n)$?

A question of Grünbaum. The Sylvester-Gallai theorem implies that if the points are not
all collinear (i.e., they determine more than one line), then they determine at least $n$
lines. Erdős showed that, for some constant $c > 0$, all integers in
$[cn^{3/2}, \binom{n}{2}]$ are possible except $\binom{n}{2} - 1$ and $\binom{n}{2} - 3$.

Solved (for all sufficiently large $n$) completely by Erdős and Salamon [ErSa88].

[Er85] Erdős, P., _Problems and results in combinatorial geometry_. Discrete geometry and
convexity (New York, 1982), Ann. New York Acad. Sci. 440 (1985), 1–11.

[ErSa88] Erdős, P. and Salamon, P., _The solution to a problem of Grünbaum_.
Canad. Math. Bull. **31** (1988), 129–138.
-/

namespace Erdos606

/-- The number of distinct lines determined by a finite point set $A$ in $\mathbb{R}^2$.
A line is the affine span of a pair of distinct points from $A$. -/
noncomputable def numLinesDetermined
    (A : Finset (ℝ²)) : ℕ :=
  Set.ncard {l : AffineSubspace ℝ (ℝ²) |
    ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ l = affineSpan ℝ ({a, b} : Set (ℝ²))}

/-- The set of achievable line counts for configurations of exactly $n$ points
in $\mathbb{R}^2$. -/
noncomputable def achievableLineCounts (n : ℕ) : Set ℕ :=
  {k | ∃ A : Finset (ℝ²),
    A.card = n ∧ numLinesDetermined A = k}

/--
Erdős Problem 606 [ErSa88]:

For sufficiently large $n$, every integer in $[c \cdot n^{3/2}, \binom{n}{2}]$ is achievable
as a line count for some configuration of $n$ points in $\mathbb{R}^2$, except for
$\binom{n}{2} - 1$ and $\binom{n}{2} - 3$.
-/
@[category research solved, AMS 52]
theorem erdos_606 :
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (∀ k : ℕ, (k : ℝ) ≥ c * (n : ℝ) ^ (3 / 2 : ℝ) →
        k ≤ n.choose 2 →
        k ≠ n.choose 2 - 1 →
        k ≠ n.choose 2 - 3 →
        k ∈ achievableLineCounts n) ∧
      n.choose 2 - 1 ∉ achievableLineCounts n ∧
      n.choose 2 - 3 ∉ achievableLineCounts n := by
  sorry

/--
Sylvester-Gallai consequence [Er85]:

For any set of $n \geq 2$ points in $\mathbb{R}^2$ that are not all collinear (i.e., they
determine more than $1$ line), the number of distinct lines determined is at least $n$.
-/
@[category research solved, AMS 52]
theorem erdos_606.variants.sylvester_gallai :
    ∀ A : Finset (ℝ²),
      A.card ≥ 2 →
      numLinesDetermined A > 1 →
      numLinesDetermined A ≥ A.card := by
  sorry

end Erdos606
