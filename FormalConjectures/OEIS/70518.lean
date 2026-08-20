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
# Value of $n$-th cyclotomic polynomial at $n$

The sequence $a(n) = \Phi_n(n)$ gives the value of the $n$-th cyclotomic polynomial evaluated
at $n$:
$$a(n) = |\Phi_n(n)|$$

*References:*
- [A070518](https://oeis.org/A070518)-/

namespace OeisA70518

open Polynomial

/-- Value of the $n$-th cyclotomic polynomial at $n$. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((cyclotomic n ℤ).eval (n : ℤ)).natAbs

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  dsimp [a]
  rw [cyclotomic_one]
  simp

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  dsimp [a]
  rw [cyclotomic_two]
  simp

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 13 := by
  dsimp [a]
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [cyclotomic_prime ℤ 3]
  simp [Finset.sum_range_succ]

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 781 := by
  dsimp [a]
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [cyclotomic_prime ℤ 5]
  simp [Finset.sum_range_succ]

open scoped Classical in
/--
$a(28341)$ is divisible by $283411^2$. What is the next $n$ such that $a(n)$ is not squarefree?
-/
@[category research open, AMS 11]
theorem conjecture :
    answer(sorry) =
      if h : ∃ n, 28341 < n ∧ ¬ Squarefree (a n) then
        some (sInf {n | 28341 < n ∧ ¬ Squarefree (a n)})
      else
        none := by
  sorry

end OeisA70518

