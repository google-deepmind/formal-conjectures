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
# Multiplicities in bitwise modular sum sequence A049802

$a(n)$ is the number of occurrences of $n$ in the sequence A049802.

*References:*
- [A383327](https://oeis.org/A383327)
-/
open Nat Finset

namespace OeisA383327

/--
The number of occurrences of $n$ in A049802.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- Define the auxiliary sequence A049802 locally.
    let A049802_val (m : ℕ) : ℕ :=
      let r := Nat.log 2 m
      -- Sum over k=1 to r. We use index i in {0, ..., r-1} such that k = i+1.
      ∑ i ∈ range r, m % (2 ^ (i + 1))

    -- Since $A049802(m) = n$ implies $m < 2^{n+1}$, we use $B = 2^{n+1}$ as a sufficient bound.
    let B : ℕ := 2 ^ (n + 1)
    (filter (fun m => A049802_val m = n) (range B)).card

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by rfl
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by rfl
@[category test, AMS 11]
theorem a_4 : a 4 = 4 := by rfl

/--
Conjecture based on OEIS comment:
For $n \le 100$, when $n \in \{1, 3, 5, 9, 15, 23, 35, 63, 65, 69\}$, there is only one $m$
such that $A049802(m) = n$, so $a(n) = 1$.

Note: The OEIS comment lists $67$ instead of $69$, but this is a typo in the OEIS comment:
the sequence terms in OEIS have $a(67) = 5$ (e.g. $A049802(147) = A049802(2055) = 67$) and
$a(69) = 1$.
-/
@[category research open, AMS 11]
theorem single_occurrence_values_le_100 :
  let S : Finset ℕ := {1, 3, 5, 9, 15, 23, 35, 63, 65, 69}
  ∀ n : ℕ, n ∈ S → a n = 1 :=
by sorry

end OeisA383327
