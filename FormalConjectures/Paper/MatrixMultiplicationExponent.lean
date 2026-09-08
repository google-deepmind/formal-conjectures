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
# The matrix multiplication exponent

The conjecture $\omega = 2$ asserts that matrix multiplication over $\mathbb{C}$ takes
$O(n^{2+\varepsilon})$ arithmetic operations for every $\varepsilon > 0$.
We use its tensor-rank formulation.

*References:*
* [CKSU05] H. Cohn et al.,
  [*Group-theoretic Algorithms for Matrix Multiplication*](https://doi.org/10.1109/SFCS.2005.39),
  FOCS 2005, 379–388, Introduction and Section 1.1.
  [Preprint](https://arxiv.org/abs/math/0511460). Used for
  `matrix_multiplication_exponent_two`.
* [CHILO18] L. Chiantini et al.,
  [*Polynomials and the exponent of matrix multiplication*](https://doi.org/10.1112/blms.12147),
  Bull. London Math. Soc. 50 (2018), 369–389, equation (1.1) and the following paragraph.
  [Preprint](https://arxiv.org/abs/1706.05074). Used for
  `matrix_multiplication_exponent_two`.
* [Strassen69] V. Strassen,
  [*Gaussian elimination is not optimal*](https://doi.org/10.1007/BF01343649),
  Numerische Mathematik 13 (1969), 354–356. Used for
  `matrix_multiplication_exponent_strassen`.
* [CW90] D. Coppersmith and S. Winograd,
  [*Matrix multiplication via arithmetic progressions*](https://doi.org/10.1016/0747-7171(90)90013-N),
  Journal of Symbolic Computation 9 (1990), 251–280. Used for
  `matrix_multiplication_exponent_coppersmith_winograd`.
* [AE26] H. Alman, V. Vassilevska Williams et al.,
  [*Improving the matrix multiplication exponent with modern optimization and
  AlphaEvolve*](https://arxiv.org/abs/2608.16884), 2026. Used for
  `matrix_multiplication_exponent_alphaevolve`.
-/

namespace MatrixMultiplicationExponent

open Filter

/-- All coefficients match $\operatorname{tr}(ABC)$ for $l = m = n = 2$. -/
@[category test, AMS 15]
theorem matrixMulTensor_two_coefficients :
    ∀ a b c : Fin 4,
      Holor.matrixMulTensor ℤ 2 2 2
        ⟨[a.val, b.val, c.val], .cons a.isLt (.cons b.isLt (.cons c.isLt .nil))⟩ =
        if a.val % 2 = b.val / 2 ∧ b.val % 2 = c.val / 2 ∧ c.val % 2 = a.val / 2
        then 1 else 0 := by
  decide

/-- All coefficients match $\operatorname{tr}(ABC)$ for $(l,m,n) = (2,3,1)$. -/
@[category test, AMS 15]
theorem matrixMulTensor_rectangular_coefficients :
    ∀ (a : Fin 6) (b : Fin 3) (c : Fin 2),
      Holor.matrixMulTensor ℤ 2 3 1
        ⟨[a.val, b.val, c.val], .cons a.isLt (.cons b.isLt (.cons c.isLt .nil))⟩ =
        if a.val % 3 = b.val ∧ c.val = a.val / 3 then 1 else 0 := by
  decide

/-- The matrix multiplication exponent is at most $3$. -/
@[category test, AMS 15 68]
theorem matrix_multiplication_exponent_le_three :
    ∀ n : ℕ, 1 ≤ n →
      ((Holor.matrixMulTensor ℂ n n n).cprank : ℝ) ≤ (n : ℝ) ^ 3 := by
  intro n _
  exact_mod_cast (by simpa [pow_succ] using Holor.cprank_matrixMulTensor_le ℂ n n n)

/-- First non-trivial bound, found by V. Strassen (1969). -/
@[category research solved, AMS 51]
theorem matrix_multiplication_exponent_strassen :
    ∀ n : ℕ, 1 ≤ n →
      ((Holor.matrixMulTensor ℂ n n n).cprank : ℝ) ≤ (n : ℝ) ^ (Real.logb 2 7) := by
  sorry

/-- Coppersmith–Winograd (1987) -/
@[category research solved, AMS 51]
theorem matrix_multiplication_exponent_coppersmith_winograd :
    ∀ n : ℕ, 1 ≤ n →
      ((Holor.matrixMulTensor ℂ n n n).cprank : ℝ) ≤ (n : ℝ) ^ (2.376 : ℝ) := by
  sorry

/-- The current best bound, found by AlphaEvolve (2026). -/
@[category research solved, AMS 51]
theorem matrix_multiplication_exponent_alphaevolve :
    ∀ n : ℕ, 1 ≤ n →
      ((Holor.matrixMulTensor ℂ n n n).cprank : ℝ) ≤ (n : ℝ) ^ (2.371177 : ℝ) := by
  sorry

/-- The conjecture $\omega = 2$ over $\mathbb{C}$: tensor rank is $O(n^{2+\varepsilon})$
for every $\varepsilon > 0$. See [CKSU05] and [CHILO18]. -/
@[category research open, AMS 15 68]
theorem matrix_multiplication_exponent_two :
    ∀ ε > (0 : ℝ),
      (fun n : ℕ ↦ ((Holor.matrixMulTensor ℂ n n n).cprank : ℝ)) =O[atTop]
        (fun n ↦ (n : ℝ) ^ (2 + ε)) := by
  sorry

end MatrixMultiplicationExponent
