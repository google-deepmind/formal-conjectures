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

open Nat Finset

/--
Numbers m such that twice the number of unordered Goldbach partitions of 2m is less than the number of unordered Goldbach partitions of 4m.
Integers m such that $2 \cdot A002375(2m) < A002375(4m)$.
-/
def A335226_condition (m : ℕ) : Prop :=
  -- A002375(N): The number of unordered Goldbach partitions of N.
  -- An unordered partition is given by $(p, N-p)$ where $p \le N/2$.
  let goldbach_count (N : ℕ) : ℕ :=
    (Finset.range (N / 2 + 1)).filter (fun p => p.Prime ∧ (N - p).Prime) |>.card

  2 * goldbach_count (2 * m) < goldbach_count (4 * m)

/--
A335226: Numbers $m$ such that $2 \cdot A002375(2m) < A002375(4m)$.
-/
noncomputable def A335226 (n : ℕ) : ℕ := n.nth A335226_condition

/--
OEIS A335226 conjecture: It is conjectured that the last term in this sequence is a(114)=22564.
This is formalized as the claim that $a_{114} = 22564$ and for all $m > 22564$, the sequence condition no longer holds.
-/
theorem A335226_conjecture :
  A335226 114 = 22564 ∧ (∀ m : ℕ, m > 22564 → ¬ A335226_condition m) := by
  sorry
