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
# Number of primes of the form $2^n \pm 2^k \pm 1$ with $0 \le k < n$

The sequence $a(n)$ counts the number of distinct primes of the form $2^n \pm 2^k \pm 1$ for
$0 \le k < n$.

*References:*
- [A196697](https://oeis.org/A196697)
-/

namespace OeisA196697

/--
Number of distinct primes of the form $2^n \pm 2^k \pm 1$ with $0 \le k < n$.
-/
def a (n : ℕ) : ℕ :=
  let candidates : Finset ℕ :=
    (Finset.range n).biUnion fun k =>
      {2 ^ n + 2 ^ k + 1, 2 ^ n + 2 ^ k - 1, 2 ^ n - 2 ^ k + 1, 2 ^ n - 2 ^ k - 1}
  (candidates.filter Nat.Prime).card

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 4 := by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 6 := by decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 7 := by decide

/--
Conjecture: all terms of this sequence are greater than $0$.
- _Lei Zhou_, Oct 05 2011
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 1 ≤ n) : 0 < a n := by
  sorry

/--
Conjecture: infinitely many elements of this sequence are equal to $0$.
- _Charles R Greathouse IV_, Nov 21 2011
-/
@[category research open, AMS 11]
theorem conjecture2 : Set.Infinite {n : ℕ | a n = 0} := by
  sorry

end OeisA196697
