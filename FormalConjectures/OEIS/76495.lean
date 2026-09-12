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
# Smallest $x$ such that $\sigma(x) \bmod x = n$

The sequence $a(n)$ is the smallest positive integer $x$ such that $\sigma_1(x) \bmod x = n$,
or $0$ if no such $x$ exists.

*References:*
- [A076495](https://oeis.org/A076495)
-/

namespace OeisA76495

open ArithmeticFunction

open Classical in
/-- Smallest positive integer $x$ such that $\sigma_1(x) \bmod x = n$, or $0$ if no such $x$ exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  if h : ∃ x, 0 < x ∧ (sigma 1 x : ℕ) % x = n then
    Nat.find h
  else
    0

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide +native
  · exact (h ⟨2, by decide +native⟩).elim

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 20 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide +native
  · exact (h ⟨20, by decide +native⟩).elim

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 4 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide +native
  · exact (h ⟨4, by decide +native⟩).elim

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 9 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide +native
  · exact (h ⟨9, by decide +native⟩).elim

/-- Value of the sequence `a` at 6. -/
@[category test, AMS 11]
theorem a_6 : a 6 = 25 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide +native
  · exact (h ⟨25, by decide +native⟩).elim

/--
At present, the 0 entry for $n = 5$ is only a conjecture.
That is, it is conjectured that there is no positive integer $x$ such that
$\sigma_1(x) \bmod x = 5$.
-/
@[category research open, AMS 11]
theorem conjecture : a 5 = 0 := by
  sorry

end OeisA76495
