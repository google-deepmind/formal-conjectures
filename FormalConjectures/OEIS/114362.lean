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

/-!
# Numerator of zeta(4n)/zeta(2n)^2 (with a(0)=2 instead of -2)

Numerator of $\zeta(4n)/\zeta(2n)^2$ (with $a(0)=2$ instead of $-2$).
The ratio $\zeta(4n)/\zeta(2n)^2$ for $n \ge 1$ is the rational number
$$ Q_n = -2 \frac{B_{4n}}{B_{2n}^2 \binom{4n}{2n}} $$
where $B_k$ is the $k$-th Bernoulli number. The sequence $a(n)$ is the numerator of $Q_n$,
with $a(0)$ defined as $2$.

*References:*
- [A114362](https://oeis.org/A114362)
-/

namespace OeisA114362

open scoped Nat Real
open Filter
open Complex

/--
The primary defining sequence `a`.
Numerator of $\zeta(4n)/\zeta(2n)^2$ (with $a(0)=2$ instead of $-2$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then
    2
  else
    let B_4n : ℚ := bernoulli (4 * n)
    let B_2n : ℚ := bernoulli (2 * n)
    let binom_qn : ℚ := ↑(Nat.choose (4 * n) (2 * n))
    let Q_n : ℚ := -2 * B_4n / (B_2n * B_2n * binom_qn)
    Q_n.num.natAbs

@[category test, AMS 11]
lemma test_a_0 : a 0 = 2 := by
  congr

@[category test, AMS 11]
lemma test_a_1 : a 1 = 2 := by
  simp_all [a]
  norm_num only [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_four, bernoulli'_two, Nat.choose]

@[category test, AMS 11]
lemma test_a_2 : a 2 = 6 := by
  delta a
  norm_num +decide [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_eq_zero_of_odd, Int.natAbs_eq_iff, Nat.choose]
  rw [bernoulli'_def]
  have α := sum_bernoulli'
  norm_num only [←eq_sub_of_add_eq' (α _ ▸ Finset.sum_range_succ _ _).symm ▸ mul_div_cancel_left₀ _, Finset.sum_range_succ, or_false, or_true, Nat.choose]

@[category test, AMS 11]
lemma test_a_3 : a 3 = 691 := by
  delta and a
  norm_num [bernoulli_eq_bernoulli'_of_ne_one, two_mul, Nat.cast_choose]
  rw [bernoulli'_def, bernoulli'_def]
  have := sum_bernoulli'
  have R M := this (M+1) ▸ Finset.sum_range_succ _ _
  norm_num only [Nat.choose, ←sub_eq_of_eq_add' (R _) ▸ mul_div_cancel_left₀ _, Finset.sum_range_succ]

/--
Conjecture: if an integer n > 1 is odd, then zeta(2n)/zeta(n)^2 is irrational. Cf. W. Kohnen (link) and my conjecture in A348829. - Thomas Ordowski, Jan 05 2022
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn_gt_one : 1 < n) (hn_odd : Odd n) :
    Irrational ((riemannZeta (2 * n : ℂ) / (riemannZeta (n : ℂ)) ^ 2).re) := by
  sorry

/-- `t n` is used in the second conjecture. -/
noncomputable def t (n : ℕ) : ℝ :=
  (riemannZeta (2 * (n : ℂ))).re / ((riemannZeta (n : ℂ)).re ^ 2)

/--
Conjecture: (1 - t(n))/(1 + t(n)) = 1/2^n + 1/3^n + 1/5^n + 1/7^n + O(1/11^n), where t(n) = zeta(2n)/zeta(n)^2. Cf. A348829. - Thomas Ordowski, Nov 13 2022
-/
@[category research open, AMS 11]
theorem conjecture2 :
    (fun n : ℕ => (1 - t n) / (1 + t n) -
      (1 / (2:ℝ)^n + 1 / (3:ℝ)^n + 1 / (5:ℝ)^n + 1 / (7:ℝ)^n))
      =O[atTop] (fun n : ℕ => 1 / (11:ℝ)^n) := by
  sorry

end OeisA114362
