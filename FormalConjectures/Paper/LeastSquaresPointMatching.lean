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
`https://doi.org/10.1007/s00453-017-0326-0

-/
namespace LeastSquaresPointMatching

/--
Consider two lists of points $A=(a_1,\ldots,a_n)$ and $B=(b_1,\ldots,b_n)$, $a_i,b_j\in \mathbb{R}^2$ of length $n$.
For any congruent copy $B'$ of $B$, we can look for the least-squares matching between $A$ and $B'$:
The permutation $\pi\in S_n$ that minimizes $\sum_{i=1}^n \lVert a_i-b'_{\pi_i}\rVert^2.$
We consider the set
$S_{\mathrm{opt}} = \{ \pi\in S_n \mid \exists B'\colon \pi \text{the unique optimal matching between $A$ and $B'$}\}$.
The conjecture is that the number of permutations in $S_{opt}$ is bounded by $O(n^d)$ for some constant $d$.

We need to count only unique optimal permutations, because there can be degenerate situations with an exponential number of optimal permutations. If the conjecture is true, it implies a polynomial-time algorithm for least-squares matching under rotations.

Remark: The optimum permutation is unaffected by positive scaling of $A$ or of $B'$, as well as translation of one of the sets.

There is a variation of the problem, where the set $A$ is smaller than $B$, and we look for the least-squares
injective mapping from $A$ to $B$ (partial matching), but now we only consider tranlations.
This is the problem considered in the two papers cited above. The conjectured bound is O(m²n²).
-/

def SumOfSquaredDistances {m n : ℕ} (A : Fin m → ℝ × ℝ) (B : Fin n → ℝ × ℝ) (π : Fin m ↪ Fin n) : ℝ :=
  ∑ i, dist (A i) (B (π i)) ^ 2

@[category research open, AMS 52]
theorem least_squares_point_matching_under_rotations_is_polynomially_bounded (d : ℕ) :
  ∃ c : ℕ, ∀ n : ℕ, ∀ A B : Fin n → ℝ × ℝ,
  |{π : Fin n ↪ Fin n | ∃ B' : Fin n → ℝ × ℝ, ∃ R : Rotation, B' = R ∘ B ∧
      (∀ π' : Fin n ↪ Fin n, π' ≠ π → SumOfSquaredDistances A B' π < SumOfSquaredDistances A B' π')}| ≤ c * n ^ d + 1 := by
  sorry
theorem least_squares_partial_point_matching_under_translations_is_polynomially_bounded (d1 d2 : ℕ) :
  ∃ c : ℕ, ∀ m n : ℕ, (m < n) → ∀ A : Fin m → ℝ × ℝ, ∀ B : Fin n → ℝ × ℝ,
  |{π : Fin m ↪ Fin n | ∃ B' : Fin n → ℝ × ℝ,
      ∃ T : ℝ × ℝ, -- translation
      (∀ i, B' i = B i + T) ∧
      (∀ π' : Fin m ↪ Fin n, π' ≠ π → SumOfSquaredDistances A B' π < SumOfSquaredDistances A B' π')}|
       ≤ c * m ^ d1 * n ^ d2 + 1 := by
  sorry
-- The conjecture is O(m²n²).

end LeastSquaresPointMatching
