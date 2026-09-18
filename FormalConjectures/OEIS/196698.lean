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
# Primes of the form $3^n \pm 3^k \pm 1$

Number of primes of the form $3^n \pm 3^k \pm 1$ with $0 \le k < n$.

*References:*
- [A196698](https://oeis.org/A196698)
-/

namespace OeisA196698

/-- Number of primes of the form $3^n \pm 3^k \pm 1$ with $0 \le k < n$. -/
def a (n : ℕ) : ℕ :=
  let p3n := 3 ^ n
  (Finset.range n).biUnion (fun k =>
    let p3k := 3 ^ k
    { p3n + p3k + 1,
      p3n + p3k - 1,
      p3n - p3k + 1,
      p3n - p3k - 1 }
  )
  |>.filter Nat.Prime
  |>.card

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 4 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 6 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 8 := by decide

/--
"Conjecture: all elements of this sequence are greater than $0$."
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 1 ≤ n) : 0 < a n := by
  sorry

/--
"I conjecture the contrary: infinitely many elements of this sequence are equal to $0$."
- Charles R Greathouse IV, Nov 21 2011
-/
@[category research open, AMS 11]
theorem conjecture2 : Set.Infinite {n : ℕ | a n = 0} := by
  sorry

end OeisA196698
