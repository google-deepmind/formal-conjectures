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
# Number of primes $p$ such that $n^n \le p \le n^n + n^2$

The sequence $a(n)$ counts the number of prime numbers in the interval $[n^n, n^n + n^2]$:
$$a(n) = |\{p \text{ prime} \mid n^n \le p \le n^n + n^2\}|$$

*References:*
- [A069922](https://oeis.org/A069922)-/

namespace OeisA69922

open Finset

/-- Number of primes $p$ such that $n^n \le p \le n^n + n^2$. -/
def a (n : ℕ) : ℕ :=
  ((Icc (n ^ n) (n ^ n + n ^ 2)).filter Nat.Prime).card

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by
  decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 4 := by
  decide +native

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by
  decide +native

/--
Question: for any $n > 0$, is there at least one prime $p$ such that $n^n \le p \le n^n + n^2$?
In this case, that would be stronger than the Schinzel conjecture: "for $m > 1$ there's at least
one prime $p$ such that $m \le p \le m + \log(m)^2$" since $n^2 < \log(n^n)^2 = n^2 \log(n)^2$.-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 0 < n) : 1 ≤ a n := by
  sorry

end OeisA69922
