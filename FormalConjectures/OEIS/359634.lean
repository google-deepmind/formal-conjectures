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
# Longest contiguous subsegment sum sequence

$a(0) = 1$, and for $n > 0$, $a(n)$ is the length of the longest contiguous block of preceding terms
summing to $n$, or $0$ if no such block exists.

*References:*
- [A359634](https://oeis.org/A359634)
-/
open List Finset

namespace OeisA359634

/--
$a(0) = 1$, and for $n > 0$, $a(n)$ is the length of the longest contiguous group of preceding
terms summing to $n$.
-/
noncomputable def a : ℕ → ℕ :=
  WellFounded.fix Nat.lt_wfRel.wf (fun n IH =>
    if n = 0 then 1
    else
      let target : ℕ := n

      -- The previous terms a(k) for k < n are computed using the induction hypothesis IH.
      let a_prev (k : ℕ) (hk : k < n) : ℕ := IH k hk

      -- The list of previous terms [a(0), a(1), ..., a(n-1)]. Fin n ensures k.val < n.
      let prefix_list : List ℕ := List.ofFn (fun k : Fin n => a_prev k.val k.is_lt)

      -- Find the maximum length of a contiguous sublist that sums to target.
      -- We iterate over all possible start indices i and end indices j such that 0 ≤ i ≤ j < n.
      let max_contiguous_length : ℕ :=
        Finset.sup (range n) fun i => -- start index i
          Finset.sup (range n) fun j => -- end index j
            if i ≤ j then
              let sublist_len := j - i + 1
              let sublist := prefix_list.drop i |>.take sublist_len
              if sublist.sum = target then
                -- The length is the number of non-zero terms in the sublist
                sublist.countP (· ≠ 0)
              else 0
            else 0

      max_contiguous_length
  )

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  trivial

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by rfl

/--
Conjecture (OEIS a, C-line): A zero has not appeared in the sequence $a(n)$.
This is equivalent to $\forall n : \mathbb{N}, a(n) \neq 0$.
-/
@[category research open, AMS 11]
theorem never_zero (n : ℕ) : a n ≠ 0 := by
  sorry

end OeisA359634
