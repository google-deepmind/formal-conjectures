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

open Nat

/--
Numbers whose prime divisors all end in the same digit.
-/
def A381159_condition (n : ℕ) : Prop :=
  Finset.card (n.primeFactors.image (fun p => p % 10)) ≤ 1

/--
A381159: Numbers whose prime divisors all end in the same digit.
-/
noncomputable def A381159 (n : ℕ) : ℕ := n.nth A381159_condition


theorem a_one : A381159 1 = 1 := by
  norm_num [ A381159]
  rewrite [Nat.nth_eq_sInf]
  norm_num [ A381159_condition]
  refine IsLeast.csInf_eq ⟨ (by exists (by ·norm_num)), fun and => And.right⟩

theorem a_two : A381159 2 = 2 := by
  norm_num[A381159]
  borelize Real
  delta A381159_condition
  use(((congr_arg _)) ? _).trans (Nat.nth_count (by bound))
  norm_num[ Finset.sum,Nat.count_succ]

theorem a_three : A381159 3 = 3 := by
  norm_num [A381159]
  nontriviality
  delta A381159_condition
  use(congr_arg _ ? _).trans (Nat.nth_count (by bound))
  norm_num[Nat.count_succ]

theorem a_four : A381159 4 = 4 := by
  norm_num[A381159]
  inhabit ℝ
  delta A381159_condition
  use(4).nth_count (by norm_num[Nat.primeFactors,Nat.primeFactorsList])|>.subst ((congr_arg _) @? _)
  norm_num[Nat.count_succ]


/--
A381159 51st All-Russian Mathematical Olympiad for Schoolchildren. Problem.
Let us call a natural number "lopsided" if it is greater than 1 and all its prime divisors end with the same digit.
Is there an increasing arithmetic progression with a difference not exceeding 2025,
consisting of 150 natural numbers, each of which is "lopsided"? (A. Chironov)

We formalize the positive answer to the question/conjecture.
The condition for "lopsided" for n > 1 is exactly A381159_condition n.
We require the starting term a to be at least 2 to ensure all terms are > 1.
-/
theorem oeis_381159_conjecture_0 :
  ∃ (a d : ℕ),
    2 ≤ a ∧ -- The starting number 'a' must be lopsided, hence > 1. All subsequent terms will also be > 1.
    1 ≤ d ∧ -- 'd' must be positive for an increasing arithmetic progression
    d ≤ 2025 ∧ -- difference not exceeding 2025
    ∀ (i : Fin 150), A381159_condition (a + i.val * d)
  := by sorry
