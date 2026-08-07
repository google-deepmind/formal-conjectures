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
# Sloping binary numbers: read array of binary numbers (right-justified) along diagonals of slope $-1$

*References:*
- [A105033](https://oeis.org/A105033)
-/

namespace OeisA105033

open Nat
open Finset

/-- The primary defining sequence `a`.
`a n` is defined by the formula:
$$a(n) = n - \sum_{k \ge 0, 2^{k+1} \le n, n \equiv k \pmod{2^{k+1}}} 2^{k+1}$$ -/
def a (n : ℕ) : ℕ :=
  n - (range n).sum (fun k => if 2^(k+1) <= n ∧ n % 2^(k+1) = k then 2^(k+1) else 0)

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by decide

end OeisA105033
