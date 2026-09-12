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
# Least $k > 0$ such that $(k+1)(k+2)\cdots(k+n) + 1$ is prime

The sequence $a(n)$ is the least positive integer $k$ such that $(k+1)(k+2)\cdots(k+n) + 1$ is
prime,
if such $k$ exists; otherwise $a(n) = 0$.

*References:*
- [A078729](https://oeis.org/A078729)
-/

namespace OeisA78729

open Classical in
/-- Least positive integer $k$ such that $(k+1)(k+2)\cdots(k+n) + 1$ is prime, or 0 if no such $k$ exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  if h : ∃ k, 0 < k ∧ (∏ i ∈ Finset.range n, (k + i + 1) + 1).Prime then
    Nat.find h
  else
    0

set_option backward.isDefEq.respectTransparency false in
/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  classical
  -- `dsimp` normalises `Finset.range 1` inside the condition but not in the `Decidable`
  -- instance, which stops `split_ifs` from firing.
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide +native
  · exact (h ⟨1, by decide +native⟩).elim

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide +native
  · exact (h ⟨1, by decide +native⟩).elim

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide +native
  · exact (h ⟨2, by decide +native⟩).elim

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide +native
  · exact (h ⟨2, by decide +native⟩).elim

/-- Value of the sequence `a` at 6. -/
@[category test, AMS 11]
theorem a_6 : a 6 = 2 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide +native
  · exact (h ⟨2, by decide +native⟩).elim

/--
$(k+1)(k+2)(k+3)(k+4) + 1 = (k^2 + 5k + 5)^2$, which is never prime. Hence $a(4) = 0$.
Conjecture: $a(n) = 0$ if and only if $n = 4$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 0 < n) : a n = 0 ↔ n = 4 := by
  sorry

end OeisA78729
