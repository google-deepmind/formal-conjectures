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

open Nat Set Finset

/-- A384237: Number of divisors $d$ of $n$ such that $d^d \equiv d \pmod n$. -/
def A384237 (n : ℕ) : ℕ :=
  (n.divisors.filter fun d : ℕ => (d ^ d) % n = d % n).card

/--
A385391: $a(n)$ is the smallest integer $k$ such that $A384237(k) = n$.
This is formalized using the set infimum ($\mathrm{sInf}$) of the preimage of $n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | A384237 k = n}

/-- A002110(n): The primorial $p_n\#$. Product of the first $n$ primes (0-indexed).
  Note: Nat.nth Nat.Prime 0 = 2, Nat.nth Nat.Prime 1 = 3, etc. -/
noncomputable def A002110 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else (Finset.range n).prod fun i => Nat.nth Nat.Prime i

theorem a_one : a 1 = 1 := sorry

theorem a_two : a 2 = 2 := sorry

theorem a_three : a 3 = 6 := sorry

theorem a_four : a 4 = 12 := sorry

/--
oeis_385391_conjecture_0: A385391 a(1) = A002110(0), a(2) = A002110(1), a(3) = A002110(2), a(6) = A002110(3), a(7) = A002110(4), a(10) = A002110(5), ...?
This conjecture is formalized as a conjunction of the listed equalities, implying a general pattern related to A065295.
-/
theorem oeis_385391_conjecture_0 :
  a 1 = A002110 0 ∧
  a 2 = A002110 1 ∧
  a 3 = A002110 2 ∧
  a 6 = A002110 3 ∧
  a 7 = A002110 4 ∧
  a 10 = A002110 5 := by
  sorry
