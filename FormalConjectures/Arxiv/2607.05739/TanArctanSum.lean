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
# Integer values of $\tan(\arctan 1 + \arctan 2 + \cdots + \arctan n)$

*References:*
- [arxiv/2607.05739](https://arxiv.org/abs/2607.05739)
  **Integer values of $\tan(\arctan 1+\arctan 2+\cdots+\arctan n)$ are rare** by *Ken Ono*
- [AMM08] T. Amdeberhan, L. A. Medina, V. H. Moll, *Arithmetical properties of a sequence of
  integers related to the arctangent function*. The Ramanujan Journal 16(2) (2008), 225-230.
-/

open Finset

namespace Arxiv.«2607.05739»

/-- $Z_n = \prod_{k=1}^n (1 + ik)$, in the Gaussian integers. -/
def gaussProd (n : ℕ) : GaussianInt := ∏ k ∈ Finset.Icc 1 n, (⟨1, (k : ℤ)⟩ : GaussianInt)

/-- $A_n = \operatorname{Re} Z_n$. -/
def A (n : ℕ) : ℤ := (gaussProd n).re

/-- $B_n = \operatorname{Im} Z_n$. -/
def B (n : ℕ) : ℤ := (gaussProd n).im

/-- $x_n = \tan\left(\sum_{k=1}^n \arctan k\right) = B_n / A_n$. -/
noncomputable def x (n : ℕ) : ℚ := (B n : ℚ) / (A n : ℚ)

/-- $x_n$ takes an integer value.

Stated as $A_n \mid B_n$ rather than as `∃ m : ℤ, x n = m`, so that it still says the right
thing if $A_n$ were ever $0$. There $x_n$ is a pole of the tangent rather than an integer, but
`(B n : ℚ) / 0` is `0` in Lean and would count as one. The two agree whenever $A_n \neq 0$,
which holds for every $n \leq 3000$. -/
def IsIntegerValue (n : ℕ) : Prop := A n ∣ B n

instance (n : ℕ) : Decidable (IsIntegerValue n) := by unfold IsIntegerValue; infer_instance

/--
**Conjecture (Amdeberhan-Medina-Moll, 2008).** For every integer $n \geq 5$, the value
$$x_n = \tan(\arctan 1 + \arctan 2 + \cdots + \arctan n)$$
is not an integer.
-/
@[category research open, AMS 11]
theorem tan_arctan_sum_not_integer :
    answer(sorry) ↔ ∀ n : ℕ, 5 ≤ n → ¬ IsIntegerValue n := by
  sorry

/-- $x_n$ satisfies $x_1 = 1$ and $x_n = \dfrac{x_{n-1} + n}{1 - n x_{n-1}}$, which is the
tangent addition formula. -/
@[category research solved, AMS 11]
theorem x_succ (n : ℕ) (hn : 1 ≤ n) :
    x (n + 1) = (x n + (n + 1)) / (1 - (n + 1) * x n) := by
  sorry

/-- $x_n$ is the tangent of the partial sum of arctangents it is named for. -/
@[category research solved, AMS 11]
theorem x_eq_tan_sum_arctan (n : ℕ) (hn : 1 ≤ n) :
    (x n : ℝ) = Real.tan (∑ k ∈ Finset.Icc 1 n, Real.arctan k) := by
  sorry

/-- The four integer values the conjecture leaves out. -/
@[category test, AMS 11]
theorem isIntegerValue_of_le_four :
    IsIntegerValue 1 ∧ IsIntegerValue 2 ∧ IsIntegerValue 3 ∧ IsIntegerValue 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- $x_1 = 1$, $x_2 = -3$, $x_3 = 0$, $x_4 = 4$. -/
@[category test, AMS 11]
theorem x_values : x 1 = 1 ∧ x 2 = -3 ∧ x 3 = 0 ∧ x 4 = 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> · rw [x, A, B]; norm_num [gaussProd, Finset.prod_Icc_succ_top]

/-- The conjecture holds at the first few values it covers. -/
@[category test, AMS 11]
theorem not_isIntegerValue_of_mem_Icc_five_ten :
    ∀ n ∈ Finset.Icc 5 10, ¬ IsIntegerValue n := by
  decide

end Arxiv.«2607.05739»
