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
# Practical numbers

A positive integer $n$ is called a *practical number* (or *panarithmic number*) if every positive
integer $m \le n$ can be represented as a sum of distinct divisors of $n$.

*References:*
- [A005153](https://oeis.org/A005153)
-/

namespace OeisA5153

/-- A positive integer $n$ is practical if every $m \le n$ can be represented as a sum of
distinct divisors of $n$. -/
def A (n : ℕ) : Prop :=
  0 < n ∧ Nat.IsPractical n

/-- $1$ is a practical number. -/
@[category test, AMS 11]
theorem a_1 : A 1 := by
  refine ⟨by decide, fun m hm => ?_⟩
  interval_cases m
  · exact ⟨∅, by simp, by simp⟩
  · exact ⟨{1}, by simp, by simp⟩

/-- $2$ is a practical number. -/
@[category test, AMS 11]
theorem a_2 : A 2 := by
  refine ⟨by decide, fun m hm => ?_⟩
  interval_cases m
  · exact ⟨∅, by simp, by simp⟩
  · exact ⟨{1}, by simp, by simp⟩
  · exact ⟨{2}, by simp, by simp⟩

/-- $4$ is a practical number. -/
@[category test, AMS 11]
theorem a_4 : A 4 := by
  refine ⟨by decide, fun m hm => ?_⟩
  have hd : Nat.divisors 4 = {1, 2, 4} := by decide
  interval_cases m
  · exact ⟨∅, by simp, by simp⟩
  · exact ⟨{1}, by rw [hd, Finset.coe_subset]; decide, by simp⟩
  · exact ⟨{2}, by rw [hd, Finset.coe_subset]; decide, by simp⟩
  · exact ⟨{1, 2}, by rw [hd, Finset.coe_subset]; decide, by decide⟩
  · exact ⟨{4}, by rw [hd, Finset.coe_subset]; decide, by simp⟩

/-- $6$ is a practical number. -/
@[category test, AMS 11]
theorem a_6 : A 6 := by
  refine ⟨by decide, fun m hm => ?_⟩
  have hd : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  interval_cases m
  · exact ⟨∅, by simp, by simp⟩
  · exact ⟨{1}, by rw [hd, Finset.coe_subset]; decide, by simp⟩
  · exact ⟨{2}, by rw [hd, Finset.coe_subset]; decide, by simp⟩
  · exact ⟨{3}, by rw [hd, Finset.coe_subset]; decide, by simp⟩
  · exact ⟨{1, 3}, by rw [hd, Finset.coe_subset]; decide, by decide⟩
  · exact ⟨{2, 3}, by rw [hd, Finset.coe_subset]; decide, by decide⟩
  · exact ⟨{6}, by rw [hd, Finset.coe_subset]; decide, by simp⟩

/-- $8$ is a practical number. -/
@[category test, AMS 11]
theorem a_8 : A 8 := by
  refine ⟨by decide, fun m hm => ?_⟩
  have hd : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  interval_cases m
  · exact ⟨∅, by simp, by simp⟩
  · exact ⟨{1}, by rw [hd, Finset.coe_subset]; decide, by simp⟩
  · exact ⟨{2}, by rw [hd, Finset.coe_subset]; decide, by simp⟩
  · exact ⟨{1, 2}, by rw [hd, Finset.coe_subset]; decide, by decide⟩
  · exact ⟨{4}, by rw [hd, Finset.coe_subset]; decide, by simp⟩
  · exact ⟨{1, 4}, by rw [hd, Finset.coe_subset]; decide, by decide⟩
  · exact ⟨{2, 4}, by rw [hd, Finset.coe_subset]; decide, by decide⟩
  · exact ⟨{1, 2, 4}, by rw [hd, Finset.coe_subset]; decide, by decide⟩
  · exact ⟨{8}, by rw [hd, Finset.coe_subset]; decide, by simp⟩

/--
Conjecture: every odd number, beginning with 3, is the sum of a prime number and a practical
number.
- Hal M. Switkay, Jan 28 2023
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    ∃ p q : ℕ, p.Prime ∧ A q ∧ n = p + q := by
  sorry

end OeisA5153
