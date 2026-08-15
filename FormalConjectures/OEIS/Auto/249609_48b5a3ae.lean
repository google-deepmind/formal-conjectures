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

import FormalConjectures.Util.ProblemImports

open Nat List

/--
A249609: $a(n)$ is the smallest $m$, $1 \le m \le n$, such that $\binom{n}{m}$ is evil (A001969); $a(n)=0$ if there is no such $m$.
An evil number is one whose population count (number of set bits in binary) is even.
-/
def a (n : ℕ) : ℕ :=
  -- Define the evil property using the equivalent of popcount via bits and list count.
  let is_evil (k : ℕ) : Bool := (k.bits.count true % 2) = 0

  -- Find the smallest $m$ in $[1, n]$ using bounded recursion.
  let rec find_min_m (m : ℕ) : ℕ :=
    if m > n then 0
    else if is_evil (n.choose m) then m
    else find_min_m (m + 1)

    -- Termination is guaranteed because m strictly increases and is bounded by n.
    termination_by n + 1 - m

  find_min_m 1


theorem a_zero : a 0 = 0 := by
  delta a
  simp_all[a.find_min_m]

theorem a_one : a 1 = 0 := by
  unfold a
  simp_all[a.find_min_m]

theorem a_two : a 2 = 0 := by
  (inhabit Int)
  delta a
  simp_all[a.find_min_m]
  norm_num[Nat.bits,List.count]
  simp_all[Nat.binaryRec]

theorem a_three : a 3 = 1 := by
  delta a
  simp_all![a.find_min_m]
  norm_num [Nat.bits,List.count]
  push_cast+decide[Nat.binaryRec]

/--
Conjecture: there are only five n: 0,1,2,7,8, for which all entries of the n-th Pascal row (A007318) are odious (A000069).

The condition that all entries of the n-th Pascal row are odious is equivalent to $a(n)=0$.
An odious number is one whose population count is odd.
-/
theorem oeis_a249609_conjecture_1 (n : ℕ) : a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  sorry
