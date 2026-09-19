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
# Smallest $n$-th power equal to a sum of consecutive immediately preceding positive $n$-th powers

Smallest $n$-th power equal to a sum of some consecutive, immediately preceding, positive $n$-th
powers, or $0$ if none.

*References:*
- [A230718](https://oeis.org/A230718)
-/

namespace OeisA230718

/-- Smallest $n$-th power equal to a sum of some consecutive, immediately preceding, positive
$n$-th powers, or $0$ if none. That is, the smallest $(k+m+1)^n$ such that
$k^n + (k+1)^n + \dots + (k+m)^n = (k+m+1)^n$ with $k > 0$ and $m > 0$, or $0$ if none. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 1 else
  let P (N : ℕ) : Prop :=
    N ≥ 3 ∧ ∃ k ∈ Finset.Icc 1 (N - 2), ∑ i ∈ Finset.Ico k N, i ^ n = N ^ n
  let N_min := sInf { N : ℕ | P N }
  if N_min = 0 then 0 else N_min ^ n

/-- Helper lemma establishing `IsLeast` for a decidable predicate on natural numbers. -/
@[category API, AMS 11]
lemma isLeast_of_lt {P : ℕ → Prop} {m : ℕ} (hm : P m) (hlt : ∀ n < m, ¬ P n) :
    IsLeast { N : ℕ | P N } m :=
  ⟨hm, fun n hn => not_lt.mp fun h => hlt n h hn⟩

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by
  dsimp [a]
  rw [IsLeast.csInf_eq (isLeast_of_lt (m := 3) (by decide) (by decide))]
  rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 25 := by
  dsimp [a]
  rw [IsLeast.csInf_eq (isLeast_of_lt (m := 5) (by decide) (by decide))]
  rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 216 := by
  dsimp [a]
  rw [IsLeast.csInf_eq (isLeast_of_lt (m := 6) (by decide) (by decide))]
  rfl

/--
Is $a(n) \ne 0$ for any $n > 3$?
-/
@[category research open, AMS 11]
theorem conjecture : answer(sorry) ↔ ∃ n > 3, a n ≠ 0 := by
  sorry

end OeisA230718
