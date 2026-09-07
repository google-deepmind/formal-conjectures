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

The conjecture $\omega = 2$ asserts that, for every $\varepsilon > 0$, two
$n \times n$ matrices over $\mathbb{C}$ can be multiplied using
$O(n^{2+\varepsilon})$ arithmetic operations. We use the equivalent formulation
in terms of the rank of the matrix multiplication tensor.

*References:*
* [CKSU05] H. Cohn, R. Kleinberg, B. Szegedy, and C. Umans,
  [*Group-theoretic Algorithms for Matrix Multiplication*](https://arxiv.org/abs/math/0511460),
  Introduction and Section 1.1.
* [CHILO18] L. Chiantini, J. D. Hauenstein, C. Ikenmeyer, J. M. Landsberg, and G. Ottaviani,
  [*Polynomials and the exponent of matrix multiplication*](https://arxiv.org/abs/1706.05074),
  Section 1.
-/

namespace MatrixMultiplicationExponent

/-- The coefficient of $A_{01}B_{10}C_{00}$ is $1$. -/
@[category test, AMS 15]
theorem matrixMulTensor_two_coefficient_one :
    Holor.matrixMulTensor ℤ 2 ⟨[1, 2, 0], by decide⟩ = 1 := by
  decide

/-- The coefficient of $A_{01}B_{10}C_{01}$ is $0$. -/
@[category test, AMS 15]
theorem matrixMulTensor_two_coefficient_zero :
    Holor.matrixMulTensor ℤ 2 ⟨[1, 2, 1], by decide⟩ = 0 := by
  decide

/-- The matrix multiplication exponent over $\mathbb{C}$ is $2$: for every
$\varepsilon > 0$, the rank of the $n \times n$ matrix multiplication tensor is
at most $C n^{2+\varepsilon}$ for all positive $n$, with $C > 0$ depending only on
$\varepsilon$. See [CKSU05] and the tensor-rank characterization in [CHILO18]. -/
@[category research open, AMS 15 68]
theorem matrix_multiplication_exponent_two :
    ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
      (Holor.cprank (Holor.matrixMulTensor ℂ n) : ℝ) ≤ C * (n : ℝ) ^ (2 + ε) := by
  sorry

end MatrixMultiplicationExponent
