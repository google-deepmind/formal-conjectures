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
# Decompositions into 2p+q for odd primes

A103151: Number of decompositions of 2n+1 into 2p+q, where p and q are both odd primes.

*References:*
- [A103151](https://oeis.org/A103151)
-/

namespace OeisA103151

/--
The primary defining sequence `a`.
`a n` is the number of decompositions of `2n+1` into `2p+q`, where `p` and `q` are both odd primes.
-/
def a (n : ℕ) : ℕ :=
  -- We count the number of odd primes $p$ that satisfy the constraints.
  -- The range $p \le n$ is sufficient, as larger $p$ would make $q \le 1$, which is not prime.
  Finset.card (Finset.filter (fun p : ℕ =>
    -- p must be an odd prime.
    Nat.Prime p ∧
    p ≠ 2 ∧
    -- Ensure the expression for $q$ is positive, so Nat subtraction is well-defined for prime $q$.
    2 * p < 2 * n + 1 ∧
    -- q = 2n+1 - 2p must be prime (and is automatically odd).
    Nat.Prime (2 * n + 1 - 2 * p)
  ) (Finset.range (n + 1)))

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
lemma test_a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
lemma test_a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
lemma test_a_3 : a 3 = 0 := by decide

@[category test, AMS 11]
lemma test_a_4 : a 4 = 1 := by decide

@[category test, AMS 11]
lemma test_a_5 : a 5 = 1 := by decide

/--
Conjecture: all items for n>=4 are greater than or equal to 1. This is a stronger conjecture than the Goldbach conjecture.
-/
@[category research open, AMS 11]
theorem main_conjecture (n : ℕ) (hn : n ≥ 4) : a n ≥ 1 := by
  sorry

end OeisA103151
