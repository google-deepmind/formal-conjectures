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
# Smallest prime $\equiv 1 \pmod n$

$$a(n) = \min \{p \in \mathbb{P} \mid p \equiv 1 \pmod n\}$$

*References:*
- [A034694](https://oeis.org/A034694)-/

namespace OeisA34694

/-- Smallest prime $\equiv 1 \pmod n$. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | Nat.Prime p ∧ n ∣ (p - 1)}

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  simp_rw [a]
  exact IsLeast.csInf_eq ⟨by decide, fun and true ↦ true.1.two_le⟩

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  dsimp [a]
  exact (Nat.isLeast_find ⟨3, by decide⟩).csInf_eq

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 7 := by
  dsimp [a]
  exact (Nat.isLeast_find ⟨7, by decide⟩).csInf_eq

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by
  dsimp [a]
  exact (Nat.isLeast_find ⟨5, by decide⟩).csInf_eq

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 11 := by
  dsimp [a]
  exact (Nat.isLeast_find ⟨11, by decide⟩).csInf_eq

/--
"Conjecture: $a(n) < n^2$ for $n > 1$. - _Thomas Ordowski_, Dec 19 2016"-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 1 < n) : a n < n ^ 2 := by
  sorry

end OeisA34694
