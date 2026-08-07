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

open Nat Finset Int BigOperators

/--
A279612: Number of ways to write $n = x^2 + y^2 + z^2 + w^2$ with $x + 2y - 2z$ a power of 4 (including $4^0 = 1$), where $x,y,z,w$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let B := Nat.sqrt n
  -- An upper bound for $|x + 2y - 2z|$ is $3B$. We use $3B+1$ as a safe bound for the powers of 4.
  let B_m := 3 * B + 1

  -- The max exponent $k$ we need is $\lfloor \log_4(B_m) \rfloor$.
  let M := Nat.log 4 B_m
  -- The finset of powers of 4 that the linear combination could equal.
  let powers_of_four : Finset ℕ :=
    (Finset.range (M + 1)).image fun k => 4 ^ k

  -- Sum over all valid quadruples (x, y, z, w) based on the upper bound B.
  (Finset.range (B + 1)).sum fun x =>
  (Finset.range (B + 1)).sum fun y =>
  (Finset.range (B + 1)).sum fun z =>
  (Finset.range (B + 1)).sum fun w =>
    if x^2 + y^2 + z^2 + w^2 = n then
      -- Calculate $m = x + 2y - 2z$ as an integer.
      let m_int : ℤ := (x : ℤ) + 2 * (y : ℤ) - 2 * (z : ℤ)

      -- Check if $m$ is a positive power of 4.
      if 0 < m_int then
        let m_nat : ℕ := m_int.toNat
        if m_nat ∈ powers_of_four then 1 else 0
      else 0
    else 0

theorem a_one : a 1 = 1 := by
  norm_num[a ·]
  rfl

theorem a_two : a 2 = 1 := by
  delta a
  norm_num+decide only

theorem a_three : a 3 = 1 := by
  delta a
  norm_num+decide only

theorem a_four : a 4 = 2 := by
  delta a
  norm_num+decide only

-- The set of special multipliers q.
private def Q : Finset ℕ := {1, 2, 3, 6, 7, 8, 12, 15, 27, 31, 47, 72, 76, 92, 111, 127}

/--
Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 16^k*q (k = 0,1,2,... and q = 1, 2, 3, 6, 7, 8, 12, 15, 27, 31, 47, 72, 76, 92, 111, 127).
-/
theorem oeis_a279612_conjecture_i :
  (∀ n : ℕ, 0 < n → 0 < a n) ∧
  (∀ n : ℕ, 0 < n → (a n = 1 ↔ ∃ k q, q ∈ Q ∧ n = 16 ^ k * q))
:= by sorry
