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

open Nat List

-- rev_base(b, n) is the natural number whose base b digits are the reverse of n's digits
/-- `rev_base b n` is the number whose base-`b` digits are the reversal of `n`'s base-`b` digits. -/
def rev_base (b n : ℕ) : ℕ := Nat.ofDigits b (Nat.digits b n |>.reverse)

/--
$a_n$ is the $n$-th term of the trajectory of $103$ under the Reverse and Add! operation carried out in base $3$, written in base $10$.
$a_0 = 103$.
$a_{n+1} = a_n + \text{rev}_3(a_n)$, where $\text{rev}_3(n)$ is the number whose base $3$ digits are the reversal of $n$'s base $3$ digits.
-/
noncomputable def A077408 : ℕ → ℕ
  | 0 => 103
  | n + 1 => A077408 n + rev_base 3 (A077408 n)

/-- A natural number $n$ is a base $b$ palindrome if its base $b$ digits read the same forwards and backwards.
This is equivalent to $n = \text{rev}_b(n)$. -/
def is_base_palindrome (b n : ℕ) : Prop := n = rev_base b n

theorem a_zero : A077408 0 = 103 := by
  rfl

theorem a_one : A077408 1 = 230 := by
  -- This requires unfolding definitions and computation, but for the purpose of
  -- defining the conjecture, we just keep the structure.
  -- If we were to run the Lean code, these would likely require a `decide` or `norm_num`
  -- with appropriate configuration for `Nat.digits` and `Nat.ofDigits`.
  sorry

theorem a_two : A077408 2 = 436 := by
  sorry

theorem a_three : A077408 3 = 776 := by
  sorry


/--
A077408 103 is conjectured to be the smallest number such that the Reverse and Add! algorithm in base 3 does not lead to a palindrome.
The conjecture formalized here is that the trajectory of 103 under this operation in base 3 never reaches a palindrome.
-/
theorem oeis_77408_conjecture_0 : ∀ n : ℕ, ¬ (is_base_palindrome 3 (A077408 n)) := by
  sorry
