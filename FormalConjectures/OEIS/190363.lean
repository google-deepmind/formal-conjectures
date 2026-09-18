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
# Sequence $a(n) = n + \lfloor n r / t \rfloor + \lfloor n s / t \rfloor$

The sequence $a(n)$ is given by $a(n) = n + \lfloor n r / t \rfloor + \lfloor n s / t \rfloor$
where $r = 1$, $s = \sqrt{5/4}$, and $t = \sqrt{4/5}$. Equivalently,
$$a(n) = 2n + \lfloor n \sqrt{5/4} \rfloor + \lfloor n/4 \rfloor.$$

*References:*
- [A190363](https://oeis.org/A190363)
-/

namespace OeisA190363

/--
The sequence $a(n) = 2n + \lfloor n \sqrt{5/4} \rfloor + \lfloor n/4 \rfloor$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  2 * n + (Int.floor ((n : ℝ) * Real.sqrt (5 / 4))).toNat + n / 4

@[category API, AMS 11]
lemma floor_mul_sqrt_five_div_four (n k : ℕ)
    (h1 : (k : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * (5 / 4))
    (h2 : (n : ℝ) ^ 2 * (5 / 4) < ((k : ℝ) + 1) ^ 2) :
    Int.floor ((n : ℝ) * Real.sqrt (5 / 4)) = k := by
  rw [Int.floor_eq_iff]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h_eq : (n : ℝ) * Real.sqrt (5 / 4) = Real.sqrt ((n : ℝ) ^ 2 * (5 / 4)) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hn]
  rw [h_eq, Int.cast_natCast]
  constructor
  · rw [← Real.sqrt_sq hk]
    exact Real.sqrt_le_sqrt h1
  · have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    rw [← Real.sqrt_sq hk1]
    exact Real.sqrt_lt_sqrt (by positivity) h2

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by
  have h := floor_mul_sqrt_five_div_four 1 1 (by norm_num) (by norm_num)
  unfold a
  rw [h]
  rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 6 := by
  have h := floor_mul_sqrt_five_div_four 2 2 (by norm_num) (by norm_num)
  unfold a
  rw [h]
  rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 9 := by
  have h := floor_mul_sqrt_five_div_four 3 3 (by norm_num) (by norm_num)
  unfold a
  rw [h]
  rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 13 := by
  have h := floor_mul_sqrt_five_div_four 4 4 (by norm_num) (by norm_num)
  unfold a
  rw [h]
  rfl

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 16 := by
  have h := floor_mul_sqrt_five_div_four 5 5 (by norm_num) (by norm_num)
  unfold a
  rw [h]
  rfl

/--
Conjecture: $a(n)$ satisfies the linear recurrence with constant coefficients
$0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1$, i.e.,
$a(n + 21) = a(n + 17) + a(n + 4) - a(n)$ for $n \ge 1$.
- _Harvey P. Dale_, Jan 28 2025

The conjecture is false: $a(140) = 471$ is the first counterexample.

Since
$\lim_{n\to\infty} \frac{a(n)}{n} = \frac{9}{4} + \frac{\sqrt{5}}{2}$ is irrational,
no linear recurrence with constant integer coefficients can hold. Indeed, it follows
from known results that if $a(n)$ satisifies a linear recurrence with constant integer coefficients
and $\lim_{n \to \infty} \frac{a_n}{n} = \alpha$ exists, then $\alpha$ must be rational.
-/
@[category research solved, AMS 11]
theorem conjecture (n : ℕ) (hn : 1 ≤ n) :
    (a (n + 21) : ℤ) = a (n + 17) + a (n + 4) - a n := by
  sorry

end OeisA190363
