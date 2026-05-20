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

/-- The term $C(6k,3k)C(3k,k)$ appearing in the sum. -/
def T_term (k : ℕ) : ℕ := (6 * k).choose (3 * k) * (3 * k).choose k

/--
A189286: $a(n):=\frac{\sum_{k=0}^n \binom{6k}{3k}\binom{3k}{k}\binom{6(n-k)}{3(n-k)}\binom{3(n-k)}{n-k}}{(2n-1)\binom{3n}{n}}$.
We define the sequence as an integer sequence, handling $n=0$ explicitly and relying on exact division for $n>0$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  if h : n = 0 then
    (-1 : ℤ) -- Explicitly defined a(0)
  else
    let numerator_nat : ℕ := Finset.sum (range (n + 1)) fun k => T_term k * T_term (n - k)

    -- Denominator: (2n - 1) * C(3n, n). The result is known to be an integer.
    let denominator : ℤ := ((2 * n : ℤ) - 1) * ((3 * n).choose n : ℤ)

    (numerator_nat : ℤ) / denominator


theorem a_zero : a 0 = -1 := by
  classical constructor

theorem a_one : a 1 = 40 := by
  constructor

theorem a_two : a 2 = 696 := by
  rfl

theorem a_three : a 3 = 23408 := by
  subsingleton


/--
Conjecture (Zhi-Wei Sun, Apr 19 2011): a(n) is an integer for every n=0,1,2,....
This conjecture states that $a(n)$ is always the result of an exact division.
Specifically, for all $n>0$, $(2n-1)\binom{3n}{n}$ divides
$\sum_{k=0}^n \binom{6k}{3k}\binom{3k}{k}\binom{6(n-k)}{3(n-k)}\binom{3(n-k)}{n-k}$.
-/
theorem oeis_a189286_conjecture_0 (n : ℕ) :
  if n = 0 then True else
    let numerator_int : ℤ := Finset.sum (range (n + 1)) fun k => (T_term k : ℤ) * (T_term (n - k) : ℤ)
    let denominator : ℤ := ((2 * n : ℤ) - 1) * ((3 * n).choose n : ℤ)
    denominator ∣ numerator_int :=
by sorry
