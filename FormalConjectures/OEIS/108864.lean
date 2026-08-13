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
# Numbers $n$ such that the perfect deficiency of $n$ is $\le 10$.

We formally define the property satisfied by elements of the sequence,
using the sum of divisors function $\sigma_1(n)$.

*References:*
- [A108864](https://oeis.org/A108864)
-/

namespace OeisA108864

open Nat Finset Int

/--
The condition for a number $n$ to be in the sequence.
It satisfies $0 < n$ and its perfect deficiency is $\le 10$, using the sum of divisors
function $\sigma_1(n)$.
-/
def A (n : ℕ) : Prop :=
  let sigmaOneN : ℕ := (Nat.divisors n).sum id
  0 < n ∧ ((sigmaOneN : ℤ) - 2 * (n : ℤ)).natAbs ≤ 10

instance : DecidablePred A := by
  unfold A
  infer_instance

/--
The primary defining sequence `a`.
`a n` is the `n`-th number (0-indexed) such that its perfect deficiency is $\le 10$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  n.nth A

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  have h1 : A 1 := by decide
  have hcnt : Nat.count A 1 = 0 := by decide
  have := Nat.nth_count (p := A) h1
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  have h2 : A 2 := by decide
  have hcnt : Nat.count A 2 = 1 := by decide
  have := Nat.nth_count (p := A) h2
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  have h3 : A 3 := by decide
  have hcnt : Nat.count A 3 = 2 := by decide
  have := Nat.nth_count (p := A) h3
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_3 : a 3 = 4 := by
  have h4 : A 4 := by decide
  have hcnt : Nat.count A 4 = 3 := by decide
  have := Nat.nth_count (p := A) h4
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by
  have h5 : A 5 := by decide
  have hcnt : Nat.count A 5 = 4 := by decide
  have := Nat.nth_count (p := A) h5
  rwa [hcnt] at this

/--
Is 1155 the last odd number in this sequence?
(1155 is the 59th term starting from 1, corresponding to `a 58 = 1155`).
-/
@[category research open, AMS 11]
theorem conjecture :
    answer(sorry) ↔ ∀ n > 58, Even (a n) := by
  sorry

end OeisA108864
