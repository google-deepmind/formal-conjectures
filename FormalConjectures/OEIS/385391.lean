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

import FormalConjecturesUtil

/-!
# Smallest integer with given count of self-power divisor congruences

$a(n)$ is the smallest integer $k$ such that the number of divisors $d \mid k$ satisfying $d^d
\equiv d \pmod k$ equals $n$.

*References:*
- [A385391](https://oeis.org/A385391)
-/
open Nat Set Finset

namespace OeisA385391

/-- A384237: Number of divisors $d$ of $n$ such that $d^d \equiv d \pmod n$. -/
def A384237 (n : ℕ) : ℕ :=
  (n.divisors.filter fun d : ℕ => (d ^ d) % n = d % n).card

/--
The smallest integer $k$ such that $A384237(k) = n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | A384237 k = n}

/-- A002110(n): The primorial $p_n\#$. Product of the first $n$ primes (0-indexed).
  Note: Nat.nth Nat.Prime 0 = 2, Nat.nth Nat.Prime 1 = 3, etc. -/
noncomputable def A002110 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else (range n).prod fun i => Nat.nth Nat.Prime i

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  unfold a
  exact IsLeast.csInf_eq ⟨by decide, fun x _ => Nat.zero_le x⟩

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  unfold a
  exact IsLeast.csInf_eq ⟨by decide, fun x hx => by
    rcases Nat.lt_or_ge x 1 with h|h
    · interval_cases x
      · revert hx; decide
    · exact h⟩

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  unfold a
  exact IsLeast.csInf_eq ⟨by decide, fun x hx => by
    rcases Nat.lt_or_ge x 2 with h|h
    · interval_cases x <;> revert hx <;> decide
    · exact h⟩

@[category test, AMS 11]
theorem a_3 : a 3 = 6 := by
  unfold a
  exact IsLeast.csInf_eq ⟨by decide, fun x hx => by
    rcases Nat.lt_or_ge x 6 with h|h
    · interval_cases x <;> revert hx <;> decide
    · exact h⟩

@[category test, AMS 11]
theorem a_4 : a 4 = 12 := by
  unfold a
  exact IsLeast.csInf_eq ⟨by decide, fun x hx => by
    rcases Nat.lt_or_ge x 12 with h|h
    · interval_cases x <;> revert hx <;> decide
    · exact h⟩

/--
a(1) = A002110(0), a(2) = A002110(1), a(3) = A002110(2), a(6) = A002110(3), a(7) = A002110(4),
a(10) = A002110(5), ...?
This conjecture is formalized as a conjunction of the listed equalities, implying a general
pattern related to A065295.
-/
@[category research open, AMS 11]
theorem a_eq_primorial :
  a 1 = A002110 0 ∧
  a 2 = A002110 1 ∧
  a 3 = A002110 2 ∧
  a 6 = A002110 3 ∧
  a 7 = A002110 4 ∧
  a 10 = A002110 5 := by
  sorry

end OeisA385391
