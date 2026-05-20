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
open Nat Finset Classical

namespace OeisA230507

/-- The condition $2m + 1$ and $2m^3 + 1$ are both prime, for $m \in \mathbb{N}$. -/
def S_condition (m : ℕ) : Prop :=
  Nat.Prime (2 * m + 1) ∧ Nat.Prime (2 * m ^ 3 + 1)

/--
A230507: Number of ways to write $n = a + b + c$ with $a \le b \le c$, where $a, b, c$ are among those numbers $m$ (terms of A230506) with $2m + 1$ and $2m^3 + 1$ both prime.
We rely on the bounds $1 \le a$ to ensure the summands are positive.
-/
noncomputable def A230507 (n : ℕ) : ℕ :=
  -- Iterate over 'a' satisfying 1 <= a <= n/3.
  Finset.sum (Finset.Icc 1 (n / 3)) fun a ↦
    -- Iterate over 'b' satisfying a <= b <= (n-a)/2.
    Finset.sum (Finset.Icc a ((n - a) / 2)) fun b ↦
      let c := n - a - b
      -- Count 1 if a, b, and c all satisfy the special prime condition.
      if S_condition a ∧ S_condition b ∧ S_condition c
      then 1
      else 0

section ConjectureDefs

/-- Condition for $x$ and $y$ in Conjecture (ii): $x > 0$ and $2x+1$ and $2x^4-1$ are both prime. -/
def P2_condition (m : ℕ) : Prop :=
  m > 0 ∧ Nat.Prime (2 * m + 1) ∧ Nat.Prime (2 * m ^ 4 - 1)

/-- Condition for $z$ in Conjecture (ii): $z > 0$ and $2z-1$ and $2z^4-1$ are both prime. Note: $2z-1$ requires $2z \ge 1$, which is true for $z>0$. -/
def Z_condition (m : ℕ) : Prop :=
  m > 0 ∧ Nat.Prime (2 * m - 1) ∧ Nat.Prime (2 * m ^ 4 - 1)

end ConjectureDefs

/-- OEIS A230507 Conjecture Part (i): $a(n) > 0$ for all $n > 2$. -/
theorem A230507_conjecture_part_i : ∀ n : ℕ, n > 2 → A230507 n > 0 := by sorry

/-- OEIS A230507 Conjecture Part (ii): Any integer $n > 8$ can be written as $x + y + z$ ($x, y, z > 0$) with $x, y$ satisfying $P2\_condition$ and $z$ satisfying $Z\_condition$. -/
theorem A230507_conjecture_part_ii :
  ∀ n : ℕ, n > 8 → ∃ (x y z : ℕ), n = x + y + z ∧ P2_condition x ∧ P2_condition y ∧ Z_condition z := by sorry

/-- oeis_230507_conjecture_2: We have verified the conjecture for n up to 10^6.

This formalizes the claim that both parts of the conjecture hold for $n$ up to $10^6$. -/
theorem oeis_230507_verified_up_to_10_pow_6 :
  (∀ n : ℕ, n > 2 ∧ n ≤ 10^6 → A230507 n > 0)
  ∧
  (∀ n : ℕ, n > 8 ∧ n ≤ 10^6 → ∃ (x y z : ℕ), n = x + y + z ∧ P2_condition x ∧ P2_condition y ∧ Z_condition z) := by sorry

end OeisA230507
