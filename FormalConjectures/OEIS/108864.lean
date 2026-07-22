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
# A108864: Perfect deficiency of n is <= 10

Numbers $n$ such that the perfect deficiency of $n$ (A109883) is $\le 10$.
We formally define the property satisfied by elements of the sequence, using the sum of divisors function $\sigma_1(n)$.

*References:*
- [A108864](https://oeis.org/A108864)
-/

namespace OeisA108864

open Nat Finset Int

/--
The condition for a number $n$ to be in the sequence.
It satisfies $0 < n$ and its perfect deficiency is $\le 10$, using the sum of divisors function $\sigma_1(n)$.
-/
def condition (n : ℕ) : Prop :=
  let sigma_one_n : ℕ := (Nat.divisors n).sum id
  0 < n ∧ ((sigma_one_n : ℤ) - 2 * (n : ℤ)).natAbs ≤ 10

/--
The primary defining sequence `a`.
`a n` is the `n`-th number (0-indexed) such that its perfect deficiency is $\le 10$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  n.nth condition

/--
Is 1155 the last odd number in this sequence?
(1155 is the 59th term starting from 1, corresponding to `a 58 = 1155`).
-/
@[category research open, AMS 11]
theorem main_conjecture :
    answer(sorry) ↔ ∀ n > 58, Even (a n) := by
  sorry

end OeisA108864
