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
# Smallest $n$-digit numbers with zeroless fourth powers

$a(n)$ is the smallest $n$-digit number whose fourth power contains no zeros in its decimal
expansion.

*References:*
- [A358340](https://oeis.org/A358340)
-/
open Nat List Set

namespace OeisA358340

/-- A number is zeroless if its decimal digits are all non-zero. -/
def is_zeroless (k : ℕ) : Prop := 0 ∉ Nat.digits 10 k

/-- Predicate for $m$ to be an $n$-digit number. Assumes $n \ge 1$. -/
def is_n_digit (m n : ℕ) : Prop := 10^(n-1) ≤ m ∧ m < 10^n

/--
The smallest $n$-digit number whose fourth power contains no zero in base 10.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  -- Define the set S of numbers satisfying the properties.
  let S : Set ℕ := { m : ℕ | is_n_digit m n ∧ is_zeroless (m ^ 4) }
  -- sInf returns the minimum element of the set S.
  sInf S

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  dsimp [a]
  refine IsLeast.csInf_eq ⟨by norm_num [is_zeroless, is_n_digit], fun x hx => hx.1.1⟩

@[category test, AMS 11]
theorem a_2 : a 2 = 11 := by
  dsimp [a]
  refine IsLeast.csInf_eq ⟨by norm_num [is_zeroless, is_n_digit], fun x hx => ?_⟩
  by_contra! h_lt
  have h_ge := hx.1.1
  interval_cases x; revert hx; norm_num [is_zeroless, is_n_digit]

@[category test, AMS 11]
theorem a_3 : a 3 = 104 := by
  dsimp [a]
  refine IsLeast.csInf_eq ⟨by norm_num [is_zeroless, is_n_digit], fun x hx => ?_⟩
  by_contra! h_lt
  have h_ge := hx.1.1
  interval_cases x <;> (revert hx; norm_num [is_zeroless, is_n_digit])

@[category test, AMS 11]
theorem a_4 : a 4 = 1027 := by
  dsimp [a]
  refine IsLeast.csInf_eq ⟨by norm_num [is_zeroless, is_n_digit], fun x hx => ?_⟩
  by_contra! h_lt
  have h_ge := hx.1.1
  interval_cases x <;> (revert hx; norm_num [is_zeroless, is_n_digit])

/--
It has been proved that there exist infinitely many zeroless squares and cubes but there is
apparently no proof for 4th powers, 5th powers, etc.

Formalized as the conjecture that the set of natural numbers whose fourth power is zeroless is
infinite.
This is equivalent to the statement that the set $\{ m : ℕ \mid \text{is\_n\_digit}(m, n) \land
\text{is\_zeroless}(m^4) \}$ is non-empty for all $n \ge 1$, ensuring $a(n)$ is defined for all
$n$.
-/
@[category research open, AMS 11]
theorem infinitely_many_zeroless_fourth_powers : Set.Infinite { m : ℕ | is_zeroless (m ^ 4) } := by
  sorry

end OeisA358340
