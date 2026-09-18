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
# Position of $n$-th partial sum of the harmonic series when jointly ranked with $\{\log(k+1)\}$

Position of $n$-th partial sum of the harmonic series when all the partial sums are jointly ranked
with the set $\{\log(k+1)\}$; complement of A206912.

*References:*
- [A206911](https://oeis.org/A206911)
-/

namespace OeisA206911

/-- Position of $n$-th partial sum of the harmonic series when all the partial sums are jointly
ranked with the set $\{\log(k+1)\}$. -/
noncomputable def a (n : ℕ) : ℕ :=
  n + (Int.floor (Real.exp (∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)) - 1)).toNat

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  norm_num [a]

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  have h : ⌊Real.exp 1 - 1⌋ = 1 := by
    rw [Int.floor_eq_iff]
    constructor <;> { norm_num; linarith [Real.exp_one_gt_d9, Real.exp_one_lt_d9] }
  have hsum : (∑ k ∈ Finset.range 1, 1 / ((k : ℝ) + 1)) = 1 := by norm_num
  unfold a
  rw [hsum, h]
  rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 5 := by
  have hexp : (4 : ℝ) < Real.exp (3 / 2) ∧ Real.exp (3 / 2) < 5 := by
    have hgt := Real.exp_one_gt_d9
    have hlt := Real.exp_one_lt_d9
    have hpos : 0 < Real.exp (3 / 2) := Real.exp_pos _
    have hsq : (Real.exp (3 / 2)) ^ 2 = (Real.exp 1) ^ 3 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      ring_nf
    constructor
    · nlinarith [sq_nonneg (Real.exp 1 - 2.7182818283)]
    · nlinarith [sq_nonneg (2.7182818286 - Real.exp 1)]
  have h : ⌊Real.exp (3 / 2) - 1⌋ = 3 := by
    rw [Int.floor_eq_iff]
    constructor <;> { norm_num; linarith [hexp.1, hexp.2] }
  have hsum : (∑ k ∈ Finset.range 2, 1 / ((k : ℝ) + 1)) = 3 / 2 := by
    norm_num [Finset.sum_range_succ]
  unfold a
  rw [hsum, h]
  rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 8 := by
  have hexp : (6 : ℝ) < Real.exp (11 / 6) ∧ Real.exp (11 / 6) < 7 := by
    have hgt := Real.exp_one_gt_d9
    have hlt := Real.exp_one_lt_d9
    have hpos : 0 < Real.exp (11 / 6) := Real.exp_pos _
    have hpow : (Real.exp (11 / 6)) ^ 6 = (Real.exp 1) ^ 11 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      ring_nf
    constructor
    · have : (6 : ℝ) ^ 6 < (Real.exp (11 / 6)) ^ 6 := by
        rw [hpow]
        calc (6 : ℝ) ^ 6 < 2.7182818283 ^ 11 := by norm_num
          _ < (Real.exp 1) ^ 11 := by gcongr
      exact lt_of_pow_lt_pow_left₀ 6 hpos.le this
    · have : (Real.exp (11 / 6)) ^ 6 < (7 : ℝ) ^ 6 := by
        rw [hpow]
        calc (Real.exp 1) ^ 11 < 2.7182818286 ^ 11 := by gcongr
          _ < (7 : ℝ) ^ 6 := by norm_num
      exact lt_of_pow_lt_pow_left₀ 6 (by norm_num) this
  have h : ⌊Real.exp (11 / 6) - 1⌋ = 5 := by
    rw [Int.floor_eq_iff]
    constructor <;> { norm_num; linarith [hexp.1, hexp.2] }
  have hsum : (∑ k ∈ Finset.range 3, 1 / ((k : ℝ) + 1)) = 11 / 6 := by
    norm_num [Finset.sum_range_succ]
  unfold a
  rw [hsum, h]
  rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 11 := by
  have hexp : (8 : ℝ) < Real.exp (25 / 12) ∧ Real.exp (25 / 12) < 9 := by
    have hgt := Real.exp_one_gt_d9
    have hlt := Real.exp_one_lt_d9
    have hpos : 0 < Real.exp (25 / 12) := Real.exp_pos _
    have hpow : (Real.exp (25 / 12)) ^ 12 = (Real.exp 1) ^ 25 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      ring_nf
    constructor
    · have : (8 : ℝ) ^ 12 < (Real.exp (25 / 12)) ^ 12 := by
        rw [hpow]
        calc (8 : ℝ) ^ 12 < 2.7182818283 ^ 25 := by norm_num
          _ < (Real.exp 1) ^ 25 := by gcongr
      exact lt_of_pow_lt_pow_left₀ 12 hpos.le this
    · have : (Real.exp (25 / 12)) ^ 12 < (9 : ℝ) ^ 12 := by
        rw [hpow]
        calc (Real.exp 1) ^ 25 < 2.7182818286 ^ 25 := by gcongr
          _ < (9 : ℝ) ^ 12 := by norm_num
      exact lt_of_pow_lt_pow_left₀ 12 (by norm_num) this
  have h : ⌊Real.exp (25 / 12) - 1⌋ = 7 := by
    rw [Int.floor_eq_iff]
    constructor <;> { norm_num; linarith [hexp.1, hexp.2] }
  have hsum : (∑ k ∈ Finset.range 4, 1 / ((k : ℝ) + 1)) = 25 / 12 := by
    norm_num [Finset.sum_range_succ]
  unfold a
  rw [hsum, h]
  rfl

/-- The difference sequence $d(n) = a(n+1) - a(n)$. -/
noncomputable def diff (n : ℕ) : ℤ :=
  (a (n + 1) : ℤ) - (a n : ℤ)

/-- The number of $3$s in the first $N$ terms of the difference sequence $d(1), \dots, d(N)$. -/
noncomputable def count3 (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range N, if diff (n + 1) = 3 then 1 else 0

/-- The number of $2$s in the first $N$ terms of the difference sequence $d(1), \dots, d(N)$. -/
noncomputable def count2 (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range N, if diff (n + 1) = 2 then 1 else 0

/--
"Conjecture: the difference sequence of A206911 consists of $2$s and $3$s, and the ratio
(number of $3$s)/(number of $2$s) tends to a number between $3.5$ and $3.6$."
-/
@[category research open, AMS 11]
theorem conjecture :
    (∀ n : ℕ, 1 ≤ n → diff n = 2 ∨ diff n = 3) ∧
    (∃ l : ℝ, 3.5 < l ∧ l < 3.6 ∧
      Filter.Tendsto (fun N : ℕ => (count3 N : ℝ) / (count2 N : ℝ)) Filter.atTop (nhds l)) := by
  sorry

end OeisA206911
