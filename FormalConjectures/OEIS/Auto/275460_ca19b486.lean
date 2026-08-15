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
open Nat Int Rat

/--
A275460: The rational-valued auxiliary function for the sequence, defined by the recurrence relation:
$a(n) = a(n-1) \cdot \frac{3(9n-7)(9n-5)(9n-2)}{n^2(3n-2)}$ for $n \ge 1$, with $a(0)=1$.
This recurrence is equivalent to the generating function definition.
-/
noncomputable def A275460_rational : ℕ → ℚ
  | 0 => 1
  | Nat.succ k =>
    let n : ℕ := k + 1
    let a_prev : ℚ := A275460_rational k
    let n_q : ℚ := n.cast
    -- Recurrence coefficient: 3 * (9n-7)(9n-5)(9n-2) / (n^2 * (3n-2))
    let num : ℚ := 3 * (9 * n_q - 7) * (9 * n_q - 5) * (9 * n_q - 2)
    let den : ℚ := n_q^2 * (3 * n_q - 2)
    a_prev * (num / den)

/--
A275460: G.f.: $\hphantom{}_3F_2([2/9, 4/9, 7/9], [1/3, 1], 729 x)$.
The coefficients are natural numbers, so we cast the rational result to $\mathbb{N}$.
We use the recurrence definition as it is the simplest algebraic representation of the D-finite series coefficients.
-/
@[simp] noncomputable def a (n : ℕ) : ℕ :=
  (A275460_rational n).floor.toNat


theorem a_zero : A275460_rational 0 = 1 := by
  norm_num [A275460_rational]

theorem a_one : A275460_rational 1 = 168 := by
  norm_num [A275460_rational]

theorem a_two : A275460_rational 2 = 72072 := by
  norm_num[A275460_rational]

theorem a_three : A275460_rational 3 = 37752000 := by
  norm_num [ A275460_rational]

/--
oeis_275460_conjecture_0: "Other hypergeometric 'blind spots' for Christol’s conjecture" - (see Bostan link).
The necessary condition for the OEIS definition `A275460_rational n` to correspond to a sequence of natural numbers is that these rational values are always integers.
This specific conjecture states that all coefficients $a(n)$ are integers.
-/
theorem A275460_is_integral (n : ℕ) : (A275460_rational n).isInt := by
  sorry
