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

open Nat Finset

/--
A264010: Number of ways to write $n$ as $x^2 + y(y+1) + z(z+1)/2$, where $x, y$ and $z$ are nonnegative integers such that $y$ or $y+1$ is prime, and $z$ or $z+1$ is prime.
-/
def A264010 (n : ℕ) : ℕ :=
  let T (z : ℕ) : ℕ := z * (z + 1) / 2
  let prime_cond (k : ℕ) : Prop := k.Prime ∨ (k + 1).Prime

  -- A loose, but sufficient upper bound for all variables is $n+1$. We use $2n+2$ for maximum safety.
  let B := 2 * n + 2

  (range B).sum fun x =>
    (range B).sum fun y =>
      (range B).sum fun z =>
        if h : x * x + y * (y + 1) + T z = n ∧ prime_cond y ∧ prime_cond z then 1 else 0


theorem a_one : A264010 1 = 0 := by
  exact rfl

theorem a_two : A264010 2 = 0 := by
  rfl

theorem a_three : A264010 3 = 1 := by
  rfl

theorem a_four : A264010 4 = 1 := by
  rfl

/--
Conjecture (i): a(n) > 0 for all n > 2, and a(n) = 1 only for n = 3, 4, 5, 6, 10, 11, 15, 20, 29, 1125.
-/
theorem oeis_264010_conjecture_i (n : ℕ) (H_n : n > 2) :
  A264010 n > 0 ∧ (A264010 n = 1 ↔ n ∈ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ)) :=
by sorry
