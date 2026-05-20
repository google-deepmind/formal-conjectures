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

open Nat BigOperators

/--
A228425: Number of ways to write $n = x + y$ ($x, y > 0$) with $x(x+1)/2 + y^2$ prime.
-/
def A228425 (n : ℕ) : ℕ :=
  (Finset.Ico 1 n).sum fun x ↦
    let y := n - x
    if Nat.Prime ((x * (x + 1) / 2) + y ^ 2) then 1 else 0

/-- $p_m(x)$, the m-gonal number, defined as $(m-2)x(x-1)/2 + x$. -/
def polygonal_number (m x : ℕ) : ℕ :=
  (m - 2) * x * (x - 1) / 2 + x

/-- The condition that for a fixed k, all natural numbers n > 1 can be written as a sum
n = x + y with x, y > 0 such that $p_k(x) + p_{k+1}(y)$ is prime. -/
def PolygonalPrimeSumCondition (k : ℕ) : Prop :=
  ∀ n : ℕ, 1 < n →
    ∃ x y : ℕ,
      0 < x ∧ 0 < y ∧ n = x + y ∧
      Nat.Prime ((polygonal_number k x) + (polygonal_number (k + 1) y))

theorem a_one : A228425 1 = 0 := by rfl
theorem a_two : A228425 2 = 1 := by sorry
theorem a_three : A228425 3 = 1 := by sorry
theorem a_four : A228425 4 = 2 := by sorry

/--
A228425 Conjecture 3: We also conjecture that any integer n > 1 can be written as x + y (x, y > 0)
with p_k(x) + p_{k+1}(y) prime, if and only if k is among 3, 39, 99.
-/
theorem oeis_a228425_conjecture_3 (k : ℕ) :
  PolygonalPrimeSumCondition k ↔ k = 3 ∨ k = 39 ∨ k = 99 :=
  by sorry
