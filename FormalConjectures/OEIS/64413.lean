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

module

public import FormalConjecturesUtil

/-!
# The EKG sequence

The EKG sequence starts with $1,2$. Each subsequent term is the least unused positive integer
sharing a factor greater than one with the preceding term. We use the official indexing from
one and extend the sequence by $a(0)=0$.

*References:*
- [OEIS A064413](https://oeis.org/A064413)
- J. C. Lagarias, E. M. Rains and N. J. A. Sloane,
  [The EKG Sequence](https://arxiv.org/abs/math/0204011)
- [Official initial terms](https://oeis.org/A064413/b064413.txt)
-/

@[expose] public section

namespace OeisA64413

/-- The values already used and the current term, which is at least two. -/
structure State where
  used : Finset ℕ
  current : ℕ
  current_gt_one : 1 < current

/-- An unused positive integer sharing a nontrivial factor with the current term. -/
def Admissible (s : State) (m : ℕ) : Prop :=
  1 < m ∧ m ∉ s.used ∧ 1 < Nat.gcd m s.current

instance (s : State) (m : ℕ) : Decidable (Admissible s m) :=
  inferInstanceAs (Decidable (1 < m ∧ m ∉ s.used ∧ 1 < Nat.gcd m s.current))

/-- A bound containing a fresh multiple of the current term. -/
def searchBound (s : State) : ℕ :=
  s.current * (s.used.sup id + 1)

/-- The admissible values at most the search bound. -/
def candidates (s : State) : Finset ℕ :=
  (Finset.range (searchBound s + 1)).filter (Admissible s)

/-- A fresh multiple proves that the finite search always has a candidate. -/
@[category API, AMS 11]
theorem candidates_nonempty (s : State) : (candidates s).Nonempty := by
  have hcur := s.current_gt_one
  have hmul : 2 * (s.used.sup id + 1) ≤ searchBound s := by
    exact Nat.mul_le_mul_right _ (by omega : 2 ≤ s.current)
  have hbound : s.used.sup id < searchBound s := by
    omega
  have hlarge : 1 < searchBound s := by
    omega
  have hfresh : searchBound s ∉ s.used := by
    intro hmem
    have hle : searchBound s ≤ s.used.sup id := Finset.le_sup (f := id) hmem
    omega
  refine ⟨searchBound s, Finset.mem_filter.mpr ⟨?_, hlarge, hfresh, ?_⟩⟩
  · exact Finset.mem_range.mpr (Nat.lt_succ_self _)
  · simpa [searchBound, Nat.mul_comm] using hcur

/-- The least admissible next value. -/
def next (s : State) : ℕ :=
  (candidates s).min' (candidates_nonempty s)

/-- The chosen value is unused and shares a nontrivial factor with the current term. -/
@[category API, AMS 11]
theorem next_admissible (s : State) : Admissible s (next s) :=
  (Finset.mem_filter.mp (Finset.min'_mem (candidates s) (candidates_nonempty s))).2

/-- Restricting the search to a proved witness bound preserves global leastness. -/
@[category API, AMS 11]
theorem next_le (s : State) {m : ℕ} (hm : Admissible s m) : next s ≤ m := by
  by_cases hbound : m ≤ searchBound s
  · exact Finset.min'_le _ _
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hm⟩)
  · have hmem := Finset.min'_mem (candidates s) (candidates_nonempty s)
    have hle := Finset.mem_range.mp (Finset.mem_filter.mp hmem).1
    change next s < searchBound s + 1 at hle
    omega

/-- Append the least unused value with a common factor greater than one. -/
def step (s : State) : State where
  used := insert (next s) s.used
  current := next s
  current_gt_one := (next_admissible s).1

/-- The state after the first $n+2$ official terms. -/
def state : ℕ → State
  | 0 => ⟨{1, 2}, 2, by decide⟩
  | n + 1 => step (state n)

/-- The EKG sequence with its official one-based indexing. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (state n).current

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 4 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 6 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 3 := by decide

@[category test, AMS 11]
theorem a_6 : a 6 = 9 := by decide

set_option maxRecDepth 8192 in
@[category test, AMS 11]
theorem a_8 : a 8 = 8 := by decide

set_option maxRecDepth 8192 in
@[category test, AMS 11]
theorem a_10 : a 10 = 5 := by decide

/-- The number of official indices through $n$ whose term lies strictly above the diagonal. -/
def aboveDiagonalCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => k < a k)).card

@[category test, AMS 11]
theorem above_diagonal_count_zero : aboveDiagonalCount 0 = 0 := by decide

@[category test, AMS 11]
theorem above_diagonal_count_five : aboveDiagonalCount 5 = 2 := by decide

@[category test, AMS 11]
theorem fifth_term_below_diagonal : a 5 < 5 := by rw [a_5]; decide

@[category test, AMS 11]
theorem eighth_term_not_above_diagonal : ¬8 < a 8 := by rw [a_8]; decide

/-- Every step preserves the used values and adds exactly the chosen new term. -/
@[category API, AMS 11]
theorem step_used (s : State) :
    (step s).used = insert (step s).current s.used ∧ (step s).current ∉ s.used := by
  exact ⟨rfl, (next_admissible s).2.1⟩

/-- OEIS quotes Thomas Ordowski's conjecture:
"Conjecture: lim #(a_n > n) / n = 1, i.e., #(a_n > n) ~ n."
Thus $\#\{1\le k\le n : a(k)>k\}/n \to 1$. -/
@[category research open, AMS 11]
theorem above_diagonal_density :
    Filter.Tendsto (fun n : ℕ => (aboveDiagonalCount n : ℝ) / (n : ℝ))
      Filter.atTop (nhds 1) := by
  sorry

end OeisA64413
