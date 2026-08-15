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

open Nat Int Finset

/--
A273021: Number of ordered ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $2xy + yz - zw - wx$ a square, where $w$ is a positive integer and $x,y,z$ are nonnegative integers with $x \le y$.
-/
def A273021 (n : ℕ) : ℕ :=
  let B : ℕ := Nat.sqrt n + 1
  (Finset.range B).sum fun x =>
    (Finset.range B).sum fun y =>
      (Finset.range B).sum fun z =>
        (Finset.range B).sum fun w =>
          -- Primary constraints filtering
          if x*x + y*y + z*z + w*w = n ∧ w > 0 ∧ x ≤ y then
            -- Calculate the quadratic form Q = 2xy + yz - zw - wx as an integer
            let Q : ℤ := 2 * (x : ℤ) * y + (y : ℤ) * z - (z : ℤ) * w - (w : ℤ) * x

            -- Check if Q is a non-negative perfect square.
            if Q ≥ 0 then
              let Q_nat := Q.natAbs
              -- A Nat m is a perfect square iff m.sqrt * m.sqrt = m
              if Q_nat.sqrt * Q_nat.sqrt = Q_nat then 1 else 0
            else
              0
          else
            0

-- Auxiliary definitions for Conjecture (i)
def a273021_M : Finset ℕ := {2, 22, 23, 30, 330}
def a273021_S0 : Finset ℕ := {1, 11, 31, 47, 55, 71, 105, 115, 119, 253, 383, 385}

/-- Predicate for $n$ belonging to the set of numbers for which $A273021(n) = 1$. -/
def a273021_is_one_value (n : ℕ) : Prop :=
  n ∈ a273021_S0 ∨
  -- 4^k * m for k >= 0 and m in M
  ∃ k : ℕ, ∃ m : ℕ, m ∈ a273021_M ∧ n = 4^k * m

/-- A273021 Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for
n = 1, 11, 31, 47, 55, 71, 105, 115, 119, 253, 383, 385, 4^k*m (k = 0,1,2,... and m = 2, 22, 23, 30, 330). -/
theorem A273021_conjecture_i (n : ℕ) (hn : n > 0) :
  A273021 n > 0 ∧ (A273021 n = 1 ↔ a273021_is_one_value n) := by sorry

-- The unproved theorems provided in the prompt, kept as placeholders:
theorem a_one : A273021 1 = 1 := by sorry
theorem a_two : A273021 2 = 1 := by sorry
theorem a_three : A273021 3 = 2 := by sorry
theorem a_four : A273021 4 = 2 := by sorry
