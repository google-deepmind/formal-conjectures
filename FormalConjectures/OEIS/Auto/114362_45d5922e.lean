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

open scoped Nat

/--
A114362: Numerator of $\zeta(4n)/\zeta(2n)^2$ (with $a(0)=2$ instead of $-2$).

The ratio $\zeta(4n)/\zeta(2n)^2$ for $n \ge 1$ is the rational number
$$ Q_n = -2 \frac{B_{4n}}{B_{2n}^2 \binom{4n}{2n}} $$
where $B_k$ is the $k$-th Bernoulli number. The sequence $a(n)$ is the numerator of $Q_n$,
with $a(0)$ defined as $2$.
-/
noncomputable def A114362 (n : ℕ) : ℕ :=
  if h : n = 0 then
    2
  else
    -- Bernoulli numbers B_k are rational numbers.
    let B_4n : ℚ := bernoulli (4 * n)
    let B_2n : ℚ := bernoulli (2 * n)
    -- Binomial coefficient $\binom{4n}{2n}$ as a rational number.
    let binom_qn : ℚ := ↑(Nat.choose (4 * n) (2 * n))

    -- The rational quantity Q_n = -2 * B_4n / (B_2n^2 * \binom{4n}{2n}).
    -- Note: B_2n is non-zero for n >= 1.
    let Q_n : ℚ := -2 * B_4n / (B_2n * B_2n * binom_qn)

    -- The numerator of the simplified rational, guaranteed to be positive for n >= 1.
    Q_n.num.natAbs


theorem a_zero : A114362 0 = 2 := by
  congr

theorem a_one : A114362 1 = 2 := by
  simp_all [A114362]
  norm_num only [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_four, bernoulli'_two,Nat.choose]

theorem a_two : A114362 2 = 6 := by
  delta A114362
  norm_num+decide[bernoulli_eq_bernoulli'_of_ne_one,bernoulli'_odd_eq_zero,Int.natAbs_eq_iff,Nat.choose]
  rw [bernoulli'_def]
  have α :=sum_bernoulli'
  norm_num only [←eq_sub_of_add_eq' (α _▸ Finset.sum_range_succ _ _).symm▸mul_div_cancel_left₀ _, Finset.sum_range_succ, or_false, or_true,Nat.choose]

theorem a_three : A114362 3 = 691 := by
  delta and A114362
  norm_num[bernoulli_eq_bernoulli'_of_ne_one, two_mul,Nat.cast_choose]
  rw[bernoulli'_def,bernoulli'_def]
  have:=sum_bernoulli'
  have R M:=this (M+1)▸ Finset.sum_range_succ _ _
  norm_num only[Nat.choose,←sub_eq_of_eq_add' (R _)▸mul_div_cancel_left₀ _, Finset.sum_range_succ]

open Complex

/--
Conjecture: if an integer $n > 1$ is odd, then $\zeta(2n)/\zeta(n)^2$ is irrational.
Cf. W. Kohnen (link) and my conjecture in A348829. - _Thomas Ordowski_, Jan 05 2022
-/
theorem oeis_114362_conjecture_0 (n : ℕ) (hn_gt_one : 1 < n) (hn_odd : Odd n) :
  Irrational ((riemannZeta (2 * n : ℂ) / (riemannZeta (n : ℂ)) ^ 2).re) :=
by sorry
