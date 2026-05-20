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

open Real Nat Finset Filter

/--
A206911: Position of $n$-th partial sum of the harmonic series when all the partial sums are jointly ranked with the set $\{\log(k+1)\}$; complement of A206912.
The $n$-th term $a(n)$ is the rank of $S(n) = \sum_{i=1}^n 1/i$ in the sorted list.
This rank is computed as $n + \lfloor \exp(S(n)) - 1 \rfloor$.
-/
noncomputable def A206911 (n : ℕ) : ℕ :=
  -- Define $S_n = \sum_{k=1}^n \frac{1}{k}$
  let S_n_real : ℝ := (range n).sum fun k => 1 / ((k : ℝ) + 1)

  -- The number of log terms less than S_n is $\lfloor e^{S_n} - 1 \rfloor$.
  let count_log_terms : ℤ := floor (exp S_n_real - 1)

  -- Final rank: n + count.
  n + count_log_terms.toNat

-- The existing theorems follow, confirming definition consistency.
theorem a_one : A206911 1 = 2 := by
  inhabit ℝ
  norm_num[A206911]
  norm_num[Nat.floor_eq_iff',Real.add_one_le_exp (1)|>.trans',Real.exp_one_lt_d9.trans]

theorem a_two : A206911 2 = 5 := by
  nontriviality
  simp_all[A206911]
  rw [←add_comm,(((Nat.floor_eq_iff' (by decide)).mpr _) :_=4)]
  norm_num[((Real.sum_le_exp_of_nonneg _) (3)).trans',lt_of_abs_lt ∘abs_lt_of_sq_lt_sq ((( Odd.strictMono_pow ⟨1, rfl⟩ Real.exp_one_lt_d9).trans ↑_).trans_le' ↑ _),←Real.exp_nat_mul, Finset.sum]
  norm_num[(Real.sum_le_exp_of_nonneg _ 7).trans',.!,Finset.sum]

theorem a_three : A206911 3 = 8 := by
  delta A206911
  norm_num [add_comm 03]
  rw[((Nat.floor_eq_iff (by bound)).2 ⟨by norm_num[(Real.sum_le_exp_of_nonneg _ 7).trans',(.!), Finset.sum], _⟩:⌊_⌋₊ = 6)]
  norm_num[ ((pow_lt_pow_iff_left₀ (Real.exp_nonneg _) ↑ _) (by decide:6 ≠0)).1 ∘(( Odd.strictMono_pow ⟨5, rfl⟩ Real.exp_one_lt_d9).trans (↑ _)).trans_le',←Real.exp_nat_mul]

theorem a_four : A206911 4 = 11 := by
  norm_num[A206911]
  rw[show⌊_⌋₊ = 8 from (Nat.floor_eq_iff (by bound)).2 ⟨by norm_num[(Real.sum_le_exp_of_nonneg _ 10).trans',(.!), Finset.sum], _⟩]
  norm_num [←Real.exp_nat_mul, (pow_lt_pow_iff_left₀ (@ Real.exp_nonneg _) (↑ _) (by decide:12 ≠0)).1 ∘ (( Odd.strictMono_pow ⟨12, rfl⟩ Real.exp_one_lt_d9).trans ↑_).trans_le']


-- Formalization of the conjecture.

/-- The difference sequence of A206911. Always an integer, should be 2 or 3 based on the conjecture. -/
noncomputable def A206911_diff (n : ℕ) : ℤ :=
  (A206911 (n + 1) : ℤ) - (A206911 n : ℤ)

/-- The number of times the difference sequence is 3, for indices $k \in \{1, \dots, N\}$. -/
noncomputable def count_threes (N : ℕ) : ℕ :=
  (range N).sum fun n => if A206911_diff (n + 1) = 3 then 1 else 0

/-- The number of terms considered is $N$. Assuming the difference is 2 or 3 for all $k \in \{1, \dots, N\}$,
the number of 2s is $N$ minus the number of 3s. -/
noncomputable def count_twos (N : ℕ) : ℕ :=
  N - count_threes N

/-- The ratio of the number of 3s to the number of 2s in the difference sequence up to index $N$. -/
noncomputable def ratio_threes_to_twos (N : ℕ) : ℝ :=
  if count_twos N = 0 then 0
  else (count_threes N : ℝ) / (count_twos N : ℝ)

/--
Conjecture: the difference sequence of A206911 consists of 2s and 3s,
and the ratio (number of 3s)/(number of 2s) tends to a number between 3.5 and 3.6.
-/
theorem oeis_a206911_conjecture :
  (∀ n : ℕ, 1 ≤ n → A206911_diff n ∈ ({2, 3} : Set ℤ)) ∧
  (∃ l : ℝ,
    3.5 < l ∧ l < 3.6 ∧
    Tendsto ratio_threes_to_twos atTop (nhds l)) := by
  sorry
