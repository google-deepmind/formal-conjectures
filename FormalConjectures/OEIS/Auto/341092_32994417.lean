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
A341092: Rows of Pascal's triangle which contain a 3-term arithmetic progression of a certain form.
The $n$-th term (for $n \ge 1$) is defined by the piecewise formula:
$$a(2k-1)=(k+2)^2-2$$
$$a(2k)=(k+3)^2-4$$
where $k = \lceil n/2 \rceil$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 -- Sequence starts at n=1
  else
    let k : ℕ := (n + 1) / 2
    if n % 2 = 1 then
      -- n is odd, a(n) = (k+2)^2 - 2
      (k + 2) ^ 2 - 2
    else
      -- n is even, a(n) = (k+3)^2 - 4
      (k + 3) ^ 2 - 4

-- Helper definition: n is a term in the sequence A341092 (for k >= 1).
def IsA341092Row (n : ℕ) : Prop := ∃ k : ℕ, k > 0 ∧ a k = n

-- Helper definition: Row n of Pascal's triangle contains a 3-term arithmetic progression.
-- Specifically, C(n, k1), C(n, k2), C(n, k3) form an AP if C(n, k1) + C(n, k3) = 2 * C(n, k2).
def RowHas3TermAP (n : ℕ) : Prop :=
  n > 0 ∧ ∃ (k1 k2 k3 : ℕ),
    k1 < k2 ∧ k2 < k3 ∧ k3 ≤ n ∧
    Nat.choose n k1 + Nat.choose n k3 = 2 * Nat.choose n k2

-- Helper definition: Row n contains a 4-term arithmetic progression.
-- This implies any AP of length > 3 exists.
def RowHas4TermAP (n : ℕ) : Prop :=
  n > 0 ∧ ∃ (k1 k2 k3 k4 : ℕ),
    k1 < k2 ∧ k2 < k3 ∧ k3 < k4 ∧ k4 ≤ n ∧
    -- The sequence C(n, ki) must have a constant difference.
    (Nat.choose n k1 + Nat.choose n k3 = 2 * Nat.choose n k2) ∧
    (Nat.choose n k2 + Nat.choose n k4 = 2 * Nat.choose n k3)

/--
A brute-force search of n<=1100 found no counterexample of either conjecture 1 or 2.
This formalizes the two underlying conjectures for all n > 0 derived from that empirical evidence.

Conjecture 1: The rows of Pascal's triangle $n > 0$ that contain a 3-term arithmetic progression are precisely $n=19$ or $n$ is a term of A341092.
Conjecture 2: No row of Pascal's triangle contains an arithmetic progression of four or more coefficients.
-/
theorem oeis_a341092_conjecture :
  (∀ n : ℕ, n > 0 → (RowHas3TermAP n ↔ n = 19 ∨ IsA341092Row n))
  ∧ (∀ n : ℕ, ¬ RowHas4TermAP n) := by sorry
