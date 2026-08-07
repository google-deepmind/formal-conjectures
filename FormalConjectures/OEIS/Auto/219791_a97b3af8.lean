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
A219791: Number of ways to write $n=x+y$ ($0<x \le y$) with $(xy)^2+1$ prime.
-/
def a (n : ℕ) : ℕ :=
  -- The range for $x$ is $1 \le x \le \lfloor n/2 \rfloor$.
  let valid_x_range := Finset.Icc 1 (n / 2)
  valid_x_range.filter (fun x : ℕ => Nat.Prime ((x * (n - x)) ^ 2 + 1)) |>.card


theorem a_one : a 1 = 0 := by sorry
theorem a_two : a 2 = 1 := by sorry
theorem a_three : a 3 = 1 := by sorry
theorem a_four : a 4 = 1 := by sorry

/-- Zhi-Wei Sun also made the following general conjecture: For any positive integer k, each sufficiently large integer n cna be written as x+y (x>0, y>0) with (xy)^{2^k}+1 prime.
-/
theorem oeis_219791_conjecture_2 :
  ∀ (k : ℕ), 0 < k →
    ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
      ∃ (x y : ℕ), 0 < x ∧ 0 < y ∧ x + y = n ∧ Nat.Prime ((x * y) ^ (2^k) + 1) := by sorry
