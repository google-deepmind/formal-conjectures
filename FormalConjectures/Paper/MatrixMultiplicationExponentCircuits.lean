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
module

public import FormalConjecturesUtil

/-!
# The matrix multiplication exponent via arithmetic circuits

The exponent $\omega$ of matrix multiplication over $\mathbb{C}$ is the infimum of the real
numbers $\tau$ such that, for every $\varepsilon > 0$, two $n \times n$ complex matrices can be
multiplied using $O(n^{\tau + \varepsilon})$ arithmetic operations [OAI26b, Section 1].
The conjecture $\omega = 2$ asserts that this is possible for every $\tau > 2$.

We count operations in straight-line programs (`Matrix.MulCircuit`). Additions, subtractions and
multiplications cost $1$. Inputs and complex constants are free. This follows the challenge
statement of [OAI26b] in the OpenAI Lean library. By [BCS97, Section 15.1], the exponent does
not change if divisions are allowed, or if operations are counted by the rank of the matrix
multiplication tensor instead.

`MulCostIsBigO τ` states that there are correct circuits with $O(n^\tau)$ operations. Thus
$\omega \le c$ is the statement `∀ τ > c, MulCostIsBigO τ`, and $\omega < c$ implies
`MulCostIsBigO c`.

*References:*
* [BCS97] P. Bürgisser, M. Clausen and M. A. Shokrollahi,
  [*Algebraic Complexity Theory*](https://doi.org/10.1007/978-3-662-03338-8),
  Grundlehren der mathematischen Wissenschaften 315, Springer, 1997, Chapter 15.
* [CKSU05] H. Cohn, R. Kleinberg, B. Szegedy and C. Umans,
  [*Group-theoretic Algorithms for Matrix Multiplication*](https://doi.org/10.1109/SFCS.2005.39),
  FOCS 2005, 379–388. [Preprint](https://arxiv.org/abs/math/0511460).
* [Str69] V. Strassen,
  [*Gaussian elimination is not optimal*](https://doi.org/10.1007/BF02165411),
  Numer. Math. 13 (1969), 354–356.
* [CW90] D. Coppersmith and S. Winograd,
  [*Matrix multiplication via arithmetic progressions*](https://doi.org/10.1016/S0747-7171(08)80013-2),
  J. Symbolic Comput. 9 (1990), 251–280.
* [DEKMRSZAVB26] E. Dupont et al.,
  [*Improving the matrix multiplication exponent with modern optimization and
  AlphaEvolve*](https://arxiv.org/abs/2608.16884), preprint, 2026.
* [OAI26a] OpenAI,
  [*Complex Matrix Multiplication Below 2.258 and Rectangular Bounds*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Complex-Matrix-Multiplication-Below-2.258-and-Rectangular-Bounds-September-24-2026/Complex-Matrix-Multiplication-Below-2.258-and-Rectangular-Bounds-September-24-2026.pdf),
  OpenAI Math Release preprint, September 24, 2026.
* [OAI26b] OpenAI,
  [*An Upper Bound of 9/4 for the Matrix Multiplication Exponent*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Matrix-Multiplication-Nine-Fourths-October-2-2026/paper.pdf),
  OpenAI Math Release preprint, October 2, 2026, Theorem 1.1. Lean challenge statement:
  [`ComparatorChallenges/MatrixMultiplication.lean`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MatrixMultiplication.lean).
-/

@[expose] public section

namespace MatrixMultiplicationExponentCircuits

open Filter

/-- There are correct arithmetic circuits that multiply two $n \times n$ complex matrices using
$O(n^\tau)$ operations. -/
def MulCostIsBigO (τ : ℝ) : Prop :=
  ∃ C : (n : ℕ) → Matrix.MulCircuit ℂ (Fin n) (Fin n) (Fin n),
    (∀ n, (C n).Correct) ∧ (fun n ↦ ((C n).cost : ℝ)) =O[atTop] fun n ↦ (n : ℝ) ^ τ

/-- Two $1 \times 1$ matrices can be multiplied with one operation. -/
@[category test, AMS 15 68]
theorem exists_mulCircuit_one :
    ∃ C : Matrix.MulCircuit ℂ (Fin 1) (Fin 1) (Fin 1), C.Correct ∧ C.cost = 1 := by
  refine ⟨⟨3, ((StraightLineProgram.nil.snoc (.input (.inl (0, 0)))).snoc
    (.input (.inr (0, 0)))).snoc (.mul 0 1), fun _ _ ↦ 2⟩, fun A B ↦ ?_, rfl⟩
  ext i k
  fin_cases i
  fin_cases k
  simp [Matrix.MulCircuit.eval, Matrix.mul_apply, StraightLineProgram.eval,
    StraightLineProgram.Gate.eval, Fin.snoc, Function.uncurry]

/-- The trivial lower bound $\omega \ge 2$: each of the $n^2$ entries of the product needs its
own operation. This checks that `MulCostIsBigO` is not vacuous. -/
@[category test, AMS 15 68]
theorem not_mulCostIsBigO_of_lt_two {τ : ℝ} (hτ : τ < 2) : ¬ MulCostIsBigO τ := by
  sorry

/-- Strassen's algorithm multiplies two $n \times n$ matrices with $O(n^{\log_2 7})$
operations [Str69]. -/
@[category research solved, AMS 15 68]
theorem mulCostIsBigO_strassen : MulCostIsBigO (Real.logb 2 7) := by
  sorry

/-- The Coppersmith–Winograd bound $\omega < 2.376$ [CW90]. -/
@[category research solved, AMS 15 68]
theorem mulCostIsBigO_coppersmith_winograd : MulCostIsBigO 2.376 := by
  sorry

/-- The bound $\omega < 2.371177$ of Dupont et al. [DEKMRSZAVB26]. -/
@[category research solved, AMS 15 68]
theorem mulCostIsBigO_alphaEvolve : MulCostIsBigO 2.371177 := by
  sorry

/-- The bound $\omega < 2.258$ over $\mathbb{C}$ [OAI26a]. -/
@[category research solved, AMS 15 68]
theorem mulCostIsBigO_two_point_two_five_eight : MulCostIsBigO 2.258 := by
  sorry

/-- The bound $\omega \le 9/4$ over $\mathbb{C}$ [OAI26b, Theorem 1.1]: for every $\tau > 9/4$,
two $n \times n$ complex matrices can be multiplied using $O(n^\tau)$ operations.

The linked Lean theorem states `omega ℂ ≤ 9 / 4`, where `omega ℂ` is the infimum of the
admissible exponents in a straight-line program model with the same gates and costs. -/
@[category research solved, AMS 15 68, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/LinearAlgebra/MatrixMultiplication/Main.lean#L14"]
theorem mulCostIsBigO_nine_fourths {τ : ℝ} (hτ : 9 / 4 < τ) : MulCostIsBigO τ := by
  sorry

/-- The conjecture $\omega = 2$ over $\mathbb{C}$: for every $\tau > 2$, two $n \times n$
complex matrices can be multiplied using $O(n^\tau)$ operations. See [CKSU05, Section 1]. -/
@[category research open, AMS 15 68]
theorem mulCostIsBigO_two {τ : ℝ} (hτ : 2 < τ) : MulCostIsBigO τ := by
  sorry

end MatrixMultiplicationExponentCircuits
