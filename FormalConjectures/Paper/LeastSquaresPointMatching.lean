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
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation

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

abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

variable {m n : ℕ}

/-- The sum of squared distances between corresponding points under a mapping $\pi$. -/
noncomputable def SumOfSquaredDistances (A : Fin m → EuclideanPlane)
                                        (B : Fin n → EuclideanPlane) (π : Fin m ↪ Fin n) : ℝ :=
  ∑ i, dist (A i) (B (π i)) ^ 2

/--
Consider two lists of points $A=(a_1,\ldots,a_m)$ and $B=(b_1,\ldots,b_n)$, with
$a_i,b_j\in \mathbb{R}^2$, of length $m$ and $n$, respectively, with $m \leq n$.
For any translated copy $B'$ of $B$, we can look for the least-squares
injective mapping $\pi$ from $A$ to $B'$ (partial matching), the mapping that minimizes
 $$\sum_{i=1}^m \lVert a_i-b'_{\pi_i}\rVert^2.$$
We consider the set
$$S_{\mathrm{opt}} = \{ \pi \mid \exists B'\colon
 \pi \text{is the unique optimal matching between $A$ and $B'$}\}.$$
The conjecture says that the number of partial matchings in $S_{opt}$ is bounded by
$O(m^{d_1}n^{d_2})$ for some constants $d_1, d_2$.
This would imply a polynomial-time algorithm for partial least-squares matching under translations.
More specifically, the conjecture is that the bound is $O(m^2n^2)$.

(We must count only unique optimal partial matchings, because there are degenerate situations with
an exponential number of optimal partial matchings, for example, if $A$ lies
on the $x$-axis and $B$ on the $y$-axis.)
If the conjecture is true, it implies a polynomial-time algorithm for finding the best translation.
-/
@[category research open, AMS 52]
theorem least_squares_partial_point_matching_under_translations_is_polynomially_bounded :
  ∃ d1 d2 : ℕ, ∃ c : ℕ, ∀ m n : ℕ, (m ≤ n) →
  ∀ A : Fin m → EuclideanPlane, ∀ B : Fin n → EuclideanPlane,
  {π : Fin m ↪ Fin n |
    ∃ T : EuclideanPlane, -- translation
    let B' := fun i => B i + T
    (∀ π' : Fin m ↪ Fin n, π' ≠ π → SumOfSquaredDistances A B' π' > SumOfSquaredDistances A B' π)}.ncard
    ≤ c * m ^ d1 * n ^ d2 + 1 -- add +1 to account for the case m=0
    := by
  sorry

/--
There is a variation of the problem, where the sets $A$ and $B$ have equal size $n$, but
we allow $B$ to be rotated to a set $B'$.
In the complete-matching case, the optimum permutation between $A$ and $B'$
is unaffected by translation of one of the sets, as well as positive scaling of $A$
or of $B'$.
Therefore, it is sufficient to consider only rotations around the origin in the conjecture.
(One may even allow rotation combined with scaling, i.e., transformation matrices of the form
$\smallmatrix{c&-s\\s&c}$ for arbitrary $c,s \in \mathbb{R}$, without changing the conjecture.)

If the conjecture is true, it implies a polynomial-time algorithm for least-squares matching under rotations.
-/
@[category research open, AMS 52]
theorem least_squares_point_matching_under_rotations_is_polynomially_bounded :
  ∃ d : ℕ, ∃ c : ℕ, ∀ n : ℕ, ∀ A B : Fin n → EuclideanPlane,
  {π : Fin n ↪ Fin n | ∃ θ : Real.Angle,
    let B' := fun i => EuclideanGeometry.o.rotation θ (B i)
    (∀ π' : Fin n ↪ Fin n, π' ≠ π → SumOfSquaredDistances A B' π' > SumOfSquaredDistances A B' π)}.ncard
    ≤ c * n ^ d + 1 -- added +1 to account for the n=0 case
    := by
  sorry

end LeastSquaresPointMatching
