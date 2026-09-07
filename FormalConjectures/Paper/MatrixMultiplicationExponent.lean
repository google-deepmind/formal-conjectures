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
  [Preprint](https://arxiv.org/abs/math/0511460).
* [CHILO18] L. Chiantini et al.,
  [*Polynomials and the exponent of matrix multiplication*](https://doi.org/10.1112/blms.12147),
  Bull. London Math. Soc. 50 (2018), 369–389, equation (1.1) and the following paragraph.
  [Preprint](https://arxiv.org/abs/1706.05074).
-/

namespace MatrixMultiplicationExponent

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

/-- The conjecture $\omega = 2$ over $\mathbb{C}$: tensor rank is $O(n^{2+\varepsilon})$
for every $\varepsilon > 0$. See [CKSU05] and [CHILO18]. -/
@[category research open, AMS 15 68]
theorem matrix_multiplication_exponent_two :
    ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
      ((Holor.matrixMulTensor ℂ n n n).cprank : ℝ) ≤ C * (n : ℝ) ^ (2 + ε) := by
  sorry

end MatrixMultiplicationExponent
