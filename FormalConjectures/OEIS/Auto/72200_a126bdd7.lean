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
open Nat List Set Classical

/--
A072200: $a(n)$ is the smallest $k$ such that $k!$ contains exactly $n$ 6's, or 0 if no such number exists.
$$a(n) = \min \{k \in \mathbb{N} \mid \text{count}(\text{'6'}, k!) = n\}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- count_sixes (m : ℕ) is the number of 6's in the decimal representation of m.
  let count_sixes (m : ℕ) : ℕ := (Nat.digits 10 m).count 6

  -- P k is the property that k! has exactly n sixes in its decimal representation.
  let P (k : ℕ) : Prop := count_sixes (Nat.factorial k) = n

  -- $S$ is the set of natural numbers $k$ such that $k!$ has exactly $n$ sixes.
  let S : Set ℕ := {k | P k}

  -- The minimum of $S$, or 0 if $S$ is empty.
  if S.Nonempty then sInf S
  else 0

/-- A072200 conjecture: It is conjectured that $a(24) = 0$,
since no factorial less than $10000$ contained just 24 sixes. -/
theorem oeis_72200_conjecture_0 : a 24 = 0 := by
  sorry
