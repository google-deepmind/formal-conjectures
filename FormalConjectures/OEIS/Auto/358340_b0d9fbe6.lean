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

open Nat List Set

/-- A number is zeroless if its decimal digits are all non-zero. -/
def is_zeroless (k : ℕ) : Prop := 0 ∉ Nat.digits 10 k

/-- Predicate for $m$ to be an $n$-digit number. Assumes $n \ge 1$. -/
def is_n_digit (m n : ℕ) : Prop := 10^(n-1) ≤ m ∧ m < 10^n

/--
A358340: $a(n)$ is the smallest $n$-digit number whose fourth power is zeroless.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  -- Define the set S of numbers satisfying the properties.
  let S : Set ℕ := { m : ℕ | is_n_digit m n ∧ is_zeroless (m ^ 4) }
  -- sInf returns the minimum element of the set S.
  sInf S

-- The provided proofs of initial terms are kept as placeholders for context,
-- although they are incomplete/non-compiling in this environment.
theorem a_one : a 1 = 1 := by
  norm_num[a]
  push_cast[is_n_digit, Eq.comm, true,is_zeroless]
  exact (IsLeast.csInf_eq (by use And.symm (by norm_num), fun and true => true.1.1)).symm

theorem a_two : a 2 = 11 := by
  delta a
  norm_num[is_n_digit,is_zeroless]
  refine IsLeast.csInf_eq ⟨.symm (by {norm_num}), fun and true => true.1.left.lt_of_ne fun and => true.right (by {bound})⟩

theorem a_three : a 3 = 104 := by
  delta a
  push_cast[is_n_digit,is_zeroless]
  use IsLeast.csInf_eq ⟨by norm_num,fun a s=>by match a with|100|101|102|103=>norm_num at* | S+104=>omega⟩

theorem a_four : a 4 = 1027 := by
  delta a
  push_cast[is_n_digit,is_zeroless,comm]
  use symm<|IsLeast.csInf_eq ⟨.symm (by norm_num),fun a s=>not_lt.1 (Nat.exists_eq_add_of_le' (s.1.1) |>.elim fun and A B=>? _)⟩
  match and with|0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15|16|17|18|19=>use(s).elim (by norm_num[A])|n+20=>_
  match n with|0|1|2|3|4|5|6=>use(s).2 (by norm_num[A])|n+7=>omega

/--
A358340 It has been proved that there exist infinitely many zeroless squares and cubes but there is apparently no proof for 4th powers, 5th powers, etc.

Formalized as the conjecture that the set of natural numbers whose fourth power is zeroless is infinite.
This is equivalent to the statement that the set $\{ m : ℕ \mid \text{is\_n\_digit}(m, n) \land \text{is\_zeroless}(m^4) \}$ is non-empty for all $n \ge 1$, ensuring $a(n)$ is defined for all $n$.
-/
theorem oeis_a358340_conjecture_k4 : Set.Infinite { m : ℕ | is_zeroless (m ^ 4) } := by
  sorry
