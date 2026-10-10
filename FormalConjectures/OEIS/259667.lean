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
# Catalan numbers modulo $6$

The sequence $a(n) = C_n \bmod 6$, where $C_n = \frac{1}{n+1} \binom{2n}{n}$ is the $n$-th
Catalan number (A000108).

*References:*
- [A259667](https://oeis.org/A259667)
-/

namespace OeisA259667

open Nat

/-- The primary sequence $a(n) = C_n \bmod 6$, where $C_n$ is the $n$-th Catalan number. -/
def a (n : ℕ) : ℕ :=
  ((2 * n).choose n / (n + 1)) % 6

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by decide

/--
It is conjectured that the only $k$ which yield $a(2^k - 1) = 1$ are $k = 0, 1$ and $5$.
-/
@[category research open, AMS 11]
theorem conjecture1 (k : ℕ) :
    a (2 ^ k - 1) = 1 ↔ k = 0 ∨ k = 1 ∨ k = 5 := by
  sorry

/--
Conjecture: The only $k$ which yield $a(2^k - 1) = 5$ are $k = 2, 8$.
-/
@[category research open, AMS 11]
theorem conjecture2 (k : ℕ) :
    a (2 ^ k - 1) = 5 ↔ k = 2 ∨ k = 8 := by
  sorry

end OeisA259667
