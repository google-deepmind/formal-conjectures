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

import FormalConjecturesUtil

/-!
# The number of least-squares matchings under rotations is polynomially bounded

*References:* Günter Rote: Partial least-squares point matching under translations.
In: 26th European Workshop on Computational Geometry (EuroCG'10), Dortmund, March 2010, pp. 249–251,
Editor: Jan Vahrenhold.
`https://page.mi.fu-berlin.de/rote/Papers/abstract/Partial+least-squares+point+matching+under+translations.html`

Rinat Ben-Avraham, Matthias Henze, Rafel Jaume, Balázs Keszegh, Orit E. Raz, Micha Sharir, Igor Tubis.
Partial-Matching RMS Distance Under Translation: Combinatorics and Algorithms. Algorithmica 80, 2400–2421 (2018).
`https://doi.org/10.1007/s00453-017-0326-0`

-/
namespace LeastSquaresPointMatching

variable {m n : ℕ}

/-- The sum of squared distances between corresponding points under a mapping $\pi$. -/
def SumOfSquaredDistances (A : Fin m → ℝ²) (B : Fin n → ℝ²) (π : Fin m ↪ Fin n) : ℝ :=
  ∑ i, dist (A i) (B (π i)) ^ 2

/--
Consider two lists of points $A=(a_1,\ldots,a_m)$ and $B=(b_1,\ldots,b_n)$, with
$a_i,b_j\in \mathbb{R}^2$, of length $m$ and $n$, respectively, with $m \leq n$.
For any congruent copy $B'$ of $B$, we can look for the least-squares
injective mapping $\pi$ from $A$ to $B'$ (partial matching), the mapping that minimizes
 $$\sum_{i=1}^m \lVert a_i-b'_{\pi_i}\rVert^2.$$
We consider the set
$S_{\mathrm{opt}} = \{ \pi \mid \exists B'\colon \pi \text{the unique optimal matching between $A$ and $B'$}\}$.
The conjecture is that the number of permutations in $S_{opt}$ is bounded by
$O(m^{d_1}n^{d_2})$ for some constants $d_1, d_2$.
This would imply a polynomial-time algorithm for partial least-squares matching under translations.
More specifically, the conjecture is that bound is O(m²n²).

We must count only unique optimal permutations, because there can be degenerate situations with
an exponential number of optimal permutations, for example, if $A$ lies on the $x$-axis and $B$ on the $y$-axis.
If the conjecture is true, it implies a polynomial-time algorithm for least-squares matching under rotations.
-/
@[category research open, AMS 52]
theorem least_squares_partial_point_matching_under_translations_is_polynomially_bounded (d1 d2 : ℕ) :
  ∃ c : ℕ, ∀ m n : ℕ, (m ≤ n) → ∀ A : Fin m → ℝ × ℝ, ∀ B : Fin n → ℝ × ℝ,
  {π : Fin m ↪ Fin n |
    ∃ T : ℝ × ℝ, -- translation
    let B' := fun i => B i + T
    (∀ π' : Fin m ↪ Fin n, π' ≠ π → SumOfSquaredDistances A B' π' > SumOfSquaredDistances A B' π)}.ncard
    ≤ c * m ^ d1 * n ^ d2 + 1 -- add +1 to account for the case m=0
    := by
  sorry
-- The specific conjecture is that this is true for d1 = d2 = 2.


/-- A rotation in Euclidean 2-space around the origin.
It is specified by the pair (cos(θ), sin(θ)) for some angle θ. -/
structure Rotation_2 where
  cos_θ : ℝ
  sin_θ : ℝ
  unit : cos_θ ^ 2 + sin_θ ^ 2 = 1

/-- Apply a rotation to a point in ℝ². -/
def applyRotation_2 (R : Rotation_2) (p : ℝ × ℝ) : ℝ × ℝ :=
  let (x, y) := p
  (x * R.cos_θ - y * R.sin_θ, x * R.sin_θ + y * R.cos_θ)

/--
There is a variation of the problem, where the sets $A$ and $B$ have equal size $n$, but
we allow $B$ to be rotated.
In the complete-matching case, the optimum permutation between $A$ and $B'$
is unaffected by positive scaling of $A$
or of $B'$, as well as translation of one of the sets.
Therefore, it is sufficient to consider only rotations around the origin in the conjecture.
(One could also omit the `unit` condition in the definition of `Rotation_2`.)
-/
@[category research open, AMS 52]
theorem least_squares_point_matching_under_rotations_is_polynomially_bounded (d : ℕ) :
  ∃ c : ℕ, ∀ n : ℕ, ∀ A B : Fin n → ℝ × ℝ,
  {π : Fin n ↪ Fin n | ∃ R : Rotation_2,
    let B' := fun i => applyRotation_2 R (B i)
    (∀ π' : Fin n ↪ Fin n, π' ≠ π → SumOfSquaredDistances A B' π' < SumOfSquaredDistances A B' π)}.ncard
    ≤ c * n ^ d + 1 -- added +1 to account for the n=0 case
    := by
  sorry

end LeastSquaresPointMatching
