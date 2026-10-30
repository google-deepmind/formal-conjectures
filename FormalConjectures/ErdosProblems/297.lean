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
# Erdős Problem 297

*References:*
- [erdosproblems.com/297](https://www.erdosproblems.com/297)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [CFHMPSV24] Conlon, D., Fox, J., He, X., Mubayi, D., Pham, H. T., Suk, A. and Verstraëte, J.,
  *A question of Erdős and Graham on Egyptian fractions*. arXiv:2404.16016 (2024).
- [LiSa24] Liu, Y. P. and Sawhney, M., *On further questions regarding unit fractions*.
  arXiv:2404.07113 (2024).
- [St24] Steinerberger, S., *On a problem involving unit fractions*. arXiv:2403.17041 (2024).
-/

@[expose] public section

open Filter
open scoped Topology

namespace Erdos297

/-- The number of $A \subseteq \{1, \ldots, N\}$ with $\sum_{n \in A} \frac{1}{n} = x$. -/
def count (x : ℚ) (N : ℕ) : ℕ :=
  {A ∈ (Finset.Icc 1 N).powerset | ∑ n ∈ A, (1 / (n : ℕ) : ℚ) = x}.card

@[category test, AMS 11]
theorem count_one_five : count 1 5 = 1 := by decide +kernel

@[category test, AMS 11]
theorem count_one_six : count 1 6 = 2 := by decide +kernel

@[category test, AMS 11]
theorem count_half_six : count (1 / 2) 6 = 2 := by decide +kernel

/--
The integral $\int_0^1 \frac{dy}{y(1 + e^{\lambda / y})}$, which equals
$\int_0^1 \frac{e^{-\lambda/y}}{1 + e^{-\lambda/y}} \frac{dy}{y}$. It diverges for
$\lambda \leq 0$ (the Lean integral is then `0`), so for $x > 0$ every solution of
`massIntegral λ = x` is positive.
-/
noncomputable def massIntegral (l : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1, 1 / (y * (1 + Real.exp (l / y)))

/-- The unique real $\lambda_x$ with `massIntegral λ_x = x`, for $x > 0$. -/
noncomputable def lambdaOf (x : ℝ) : ℝ :=
  sInf {l : ℝ | massIntegral l = x}

/--
The constant $\gamma^* / \log 2 = 0.91\cdots$ of [LiSa24], where $\lambda^* = \lambda_1$ and
$\gamma^* = \lambda^* + \int_0^1 \log(1 + e^{-\lambda^*/y})\,dy$. Numerically
$\lambda^* \approx 0.127191$ and $\gamma^* \approx 0.631573$.
-/
noncomputable def erdos_297.answer : ℝ :=
  (lambdaOf 1 + ∫ y in (0 : ℝ)..1, Real.log (1 + Real.exp (-lambdaOf 1 / y))) / Real.log 2

/--
Let $N\geq 1$. How many $A\subseteq \{1,\ldots,N\}$ are there such that
$\sum_{n\in A}\frac{1}{n}=1$?

Liu and Sawhney [LiSa24] proved that the count is $2^{(0.91\cdots+o(1))N}$, where $0.91\cdots$ is
an explicit number defined as the solution to a certain integral equation; independently the same
asymptotic was proved by Conlon, Fox, He, Mubayi, Pham, Suk, and Verstraëte [CFHMPSV24]. We
formalise the question as asking for the exponential growth rate
$\lim_{N\to\infty} \frac{1}{N}\log_2 \#\{A\}$. The first conjunct is the existence and
uniqueness of $\lambda^*$, which [LiSa24] state with the theorem.
-/
@[category research solved, question value, AMS 11]
theorem erdos_297 : (∃! l : ℝ, massIntegral l = 1) ∧
    Tendsto (fun N : ℕ => Real.logb 2 (count 1 N) / N) atTop (𝓝 erdos_297.answer) := by
  sorry

/--
Steinerberger [St24] proved that, for $N$ sufficiently large, the number of
$A \subseteq \{1, \ldots, N\}$ with $\sum_{n\in A}\frac{1}{n} \leq 1$ is at most $2^{0.93N}$.
-/
@[category research solved, AMS 11]
theorem erdos_297.variants.steinerberger : ∀ᶠ N : ℕ in atTop,
    ({A ∈ (Finset.Icc 1 N).powerset | ∑ n ∈ A, (1 / (n : ℕ) : ℚ) ≤ 1}.card : ℝ) ≤
      2 ^ (0.93 * N : ℝ) := by
  sorry

/--
The binary-entropy exponent $c_x = \int_0^1 h\left(\frac{1}{1 + e^{\lambda_x / y}}\right) dy$ of
[CFHMPSV24], where $h$ is the binary entropy in bits.
-/
noncomputable def exponentOf (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1, Real.binEntropy (1 / (1 + Real.exp (lambdaOf x / y))) / Real.log 2

/--
Conlon, Fox, He, Mubayi, Pham, Suk, and Verstraëte [CFHMPSV24] prove more generally, for any
$x\in \mathbb{Q}_{>0}$, that the number of $A\subseteq \{1,\ldots,N\}$ such that
$\sum_{n\in A}\frac{1}{n}=x$ is $2^{(c_x + o(1))N}$, with $c_x$ as in `exponentOf`.
-/
@[category research solved, AMS 11]
theorem erdos_297.variants.general (x : ℚ) (hx : 0 < x) : (∃! l : ℝ, massIntegral l = x) ∧
    Tendsto (fun N : ℕ => Real.logb 2 (count x N) / N) atTop (𝓝 (exponentOf x)) := by
  sorry

end Erdos297
