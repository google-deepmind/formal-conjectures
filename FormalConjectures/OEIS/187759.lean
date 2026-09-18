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
# Number of ways to write $n = x + y$ ($0 < x < y < n$) with $6x \pm 1$ and $6y \pm 1$ prime

The sequence $a(n)$ counts the number of ways to write $n = x + y$ with $0 < x < y < n$ such that
$6x - 1$, $6x + 1$, $6y - 1$, and $6y + 1$ are all prime numbers.

*References:*
- [A187759](https://oeis.org/A187759)
- [Conjectures involving primes and quadratic forms](https://arxiv.org/abs/1211.1588)
  by *Zhi-Wei Sun*, arXiv:1211.1588 (2012)
-/

namespace OeisA187759

/--
The number of ways to write $n = x + y$ ($0 < x < y < n$) with $6x - 1$, $6x + 1$, $6y - 1$,
and $6y + 1$ all prime.
-/
def a (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.Icc 1 ((n - 1) / 2),
    let y := n - x
    if Nat.Prime (6 * x - 1) ∧ Nat.Prime (6 * x + 1) ∧
       Nat.Prime (6 * y - 1) ∧ Nat.Prime (6 * y + 1)
    then 1 else 0

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by decide

/-- Value of the sequence `a` at 8. -/
@[category test, AMS 11]
theorem a_8 : a 8 = 2 := by decide

/--
Conjecture: If $n > 200$ is not among $211, 226, 541, 701$, then $a(n) > 0$.
- _Zhi-Wei Sun_, Jan 03 2013
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 200 < n) (hnot : n ∉ ({211, 226, 541, 701} : Finset ℕ)) :
    0 < a n := by
  sorry

end OeisA187759
