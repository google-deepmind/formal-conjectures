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
module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Order.Monotone.Basic

@[expose] public section

/-!
# Sylvester's sequence

Sylvester's sequence $2, 3, 7, 43, 1807, \dots$
([OEIS A000058](https://oeis.org/A000058)) is defined by $s_0 = 2$ and
$s_{n+1} = s_n^2 - s_n + 1$. Its reciprocals sum to $1$:
$$\frac{1}{2} + \frac{1}{3} + \frac{1}{7} + \frac{1}{43} + \frac{1}{1807} + \cdots = 1.$$
-/

namespace Nat

/--
Sylvester's sequence $2, 3, 7, 43, 1807, \dots$, defined by $s_0 = 2$ and
$s_{n+1} = s_n^2 - s_n + 1$.

The subtraction is truncated, but `Nat.sylvester_le_sq` shows it never truncates.
-/
def sylvester : ℕ → ℕ
  | 0 => 2
  | n + 1 => sylvester n ^ 2 - sylvester n + 1

@[simp]
theorem sylvester_zero : sylvester 0 = 2 := rfl

theorem sylvester_succ (n : ℕ) :
    sylvester (n + 1) = sylvester n ^ 2 - sylvester n + 1 := rfl

theorem two_le_sylvester (n : ℕ) : 2 ≤ sylvester n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : sylvester n + 2 ≤ sylvester n ^ 2 := by nlinarith
    rw [sylvester_succ]
    omega

theorem sylvester_pos (n : ℕ) : 0 < sylvester n :=
  lt_of_lt_of_le (by norm_num) (two_le_sylvester n)

/-- The subtraction in `Nat.sylvester_succ` never truncates. -/
theorem sylvester_le_sq (n : ℕ) : sylvester n ≤ sylvester n ^ 2 := by
  have := two_le_sylvester n
  nlinarith

theorem sylvester_lt_sylvester_succ (n : ℕ) : sylvester n < sylvester (n + 1) := by
  have h₀ := two_le_sylvester n
  have h : sylvester n + sylvester n ≤ sylvester n ^ 2 := by nlinarith
  rw [sylvester_succ]
  omega

theorem strictMono_sylvester : StrictMono sylvester :=
  strictMono_nat_of_lt_succ sylvester_lt_sylvester_succ

@[simp]
theorem sylvester_one : sylvester 1 = 3 := rfl

@[simp]
theorem sylvester_two : sylvester 2 = 7 := rfl

@[simp]
theorem sylvester_three : sylvester 3 = 43 := rfl

@[simp]
theorem sylvester_four : sylvester 4 = 1807 := rfl

end Nat
