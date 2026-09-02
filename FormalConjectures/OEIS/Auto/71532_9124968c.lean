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

open BigOperators Int Real

/--
A071532: $a(n) = (-1) \cdot \sum_{k=1}^n (-1)^{\lfloor (3/2)^k \rfloor}$.
The sequence is defined over $\mathbb{Z}$, and empirically non-negative.
-/
noncomputable def a (n : ℕ) : ℤ :=
  -- Summing over k=1 to n is equivalent to summing over k'=0 to n-1, where term index is k'+1.
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      -- Since k ≥ 1, exponent_int is non-negative. We use Int.toNat for the exponent of Int^Nat power.
      (-1 : ℤ) ^ exponent_int.toNat

theorem a_one : a 1 = 1 := by
  norm_num[a]

theorem a_two : a 2 = 0 := by
  delta a
  simp only [Finset.sum_range_succ, Finset.sum_empty, add_zero, neg_add_rev]
  have h1 : floor ((3/2 : ℝ)^1) = 1 := by norm_num
  have h2 : floor ((3/2 : ℝ)^2) = 2 := by norm_num
  simp [h1, h2]
  norm_num

theorem a_three : a 3 = 1 := by
  delta a
  simp only [Finset.sum_range_succ, Finset.sum_empty, add_zero, neg_add_rev, Nat.cast_two, Nat.cast_one]
  have h1 : floor ((3/2 : ℝ)^1) = 1 := by norm_num
  have h2 : floor ((3/2 : ℝ)^2) = 2 := by norm_num
  have h3 : floor ((3/2 : ℝ)^3) = 3 := by norm_num
  simp [h1, h2, h3]
  norm_num

theorem a_four : a 4 = 2 := by
  delta a
  simp only [Finset.sum_range_succ, Finset.sum_empty, add_zero, neg_add_rev, Nat.cast_two, Nat.cast_one]
  have h1 : floor ((3/2 : ℝ)^1) = 1 := by norm_num
  have h2 : floor ((3/2 : ℝ)^2) = 2 := by norm_num
  have h3 : floor ((3/2 : ℝ)^3) = 3 := by norm_num
  have h4 : floor ((3/2 : ℝ)^4) = 5 := by norm_num
  simp [h1, h2, h3, h4]
  norm_num

/--
Conjecture: Asymptotically, $a(n) > \sqrt{n}$.
Verbatim OEIS comment: "Is a(n)>0? For n large enough does a(n)>sqrt(n) always hold?"
-/
theorem oeis_71532_conjecture_0 : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ) := by
  sorry
