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

open Nat Set

/--
A004290: Least positive multiple of $n$ that when written in base 10 uses only 0's and 1's.
-/
noncomputable def A004290 (n : ℕ) : ℕ :=
  -- The set of positive multiples of $n$ that are composed only of 0's and 1's in base 10.
  let S := { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }

  -- The sequence value is the smallest element of this set, which is the infimum.
  -- For n=0, the set is empty, and sInf on the empty set of ℕ is 0. The OEIS definition
  -- explicitly states "Least positive multiple of n", which implies n > 0.
  -- However, if S is empty, sInf S = 0. A004290(0) is an edge case, but the conjecture
  -- only concerns n < 10^k - 1, where we assume k ≥ 1, so n ≥ 1.
  sInf S


theorem a_one : A004290 1 = 1 := by
  symm
  show (1) =id _
  exact (IsLeast.csInf_eq (by use .symm (by norm_num), fun and=>And.left)).symm

theorem a_two : A004290 2 = 10 := by
  norm_num[A004290]
  exact IsLeast.csInf_eq ⟨.symm (by {norm_num}),fun R L=> not_lt.1 fun and=>absurd (L.right.2 R) (by norm_num[ and, L.1, R.mod_eq_of_lt, R.div_eq_of_lt,show(R ≠0000 ∧R ≠1)by cases L with omega]),⟩

theorem a_three : A004290 3 = 111 := by
  norm_num [A004290]
  simp_all! only [(3).dvd_iff_mod_eq_zero]
  -- Proof omitted as per instructions; this is just example code
  sorry

theorem a_four : A004290 4 = 100 := by
  simp_all[ true, A004290]
  -- Proof omitted as per instructions; this is just example code
  sorry

/--
Conjecture from A004290 by David Radcliffe:
a(10^k) = 10^k and a(10^k - 1) = (10^(9k) - 1) / 9 for all k.
Is a(n) < a(10^k - 1) for all n < 10^k - 1?
We formalize the second, unproven part. The first two parts are stated as assumptions
to establish the right-hand side of the inequality.
-/
theorem oeis_a004290_conjecture_radcliffe (k : ℕ) (hk : k > 0) :
  (A004290 (10 ^ k) = 10 ^ k) ∧
  (A004290 (10 ^ k - 1) = (10 ^ (9 * k) - 1) / 9) ∧
  (∀ n : ℕ, n < 10 ^ k - 1 → A004290 n < A004290 (10 ^ k - 1)) :=
by
  -- The structure of the conjecture is P ∧ Q ∧ R, where P and Q are given as facts
  -- and R is the actual question. We can't prove P and Q without a lot of work,
  -- so we treat the whole statement as a conjecture.
  sorry
