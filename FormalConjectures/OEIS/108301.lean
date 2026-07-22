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
# Digital sum of the Fermat number $2^{2^n} + 1$

`a n` is the digital sum of the Fermat number $2^{2^n} + 1$.
The conjecture asks if there are any prime numbers in this sequence beyond $n=11$.

*References:*
- [A108301](https://oeis.org/A108301)
-/

namespace OeisA108301

/-- The primary defining sequence `a`.
`a n` is the digital sum of the Fermat number $2^{2^n} + 1$. -/
def a (n : ℕ) : ℕ :=
  (Nat.digits 10 (2 ^ 2 ^ n + 1)).sum

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
lemma test_a_0 : a 0 = 3 := by native_decide

@[category test, AMS 11]
lemma test_a_1 : a 1 = 5 := by native_decide

@[category test, AMS 11]
lemma test_a_2 : a 2 = 8 := by native_decide

@[category test, AMS 11]
lemma test_a_3 : a 3 = 14 := by native_decide

@[category test, AMS 11]
lemma test_a_4 : a 4 = 26 := by native_decide

/-- a(0), a(1), a(5), a(6), a(7) and a(11) are primes. -/
@[category textbook, AMS 11]
theorem primes_in_a :
    Nat.Prime (a 0) ∧ Nat.Prime (a 1) ∧ Nat.Prime (a 5) ∧
    Nat.Prime (a 6) ∧ Nat.Prime (a 7) ∧ Nat.Prime (a 11) := by
  sorry

/-- a(0), a(1), a(5), a(6), a(7) and a(11) are primes. Are there any more? -/
@[category research open, AMS 11]
theorem main_conjecture : answer(sorry) ↔ ∃ n > 11, Nat.Prime (a n) := by
  sorry

end OeisA108301
