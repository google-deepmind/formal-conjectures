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
# The Yellowstone permutation

The Yellowstone permutation starts with $1,2,3$. Each subsequent term is the least unused
positive integer coprime to the preceding term and sharing a factor greater than one with the
term before that. We use the official indexing from one and extend the sequence by $a(0)=0$.

*References:*
- [OEIS A098550](https://oeis.org/A098550)
- D. L. Applegate et al., [The Yellowstone Permutation](https://arxiv.org/abs/1501.01669)
- [Official initial terms](https://oeis.org/A098550/b098550.txt)
-/

@[expose] public section

namespace OeisA98550

/-- The used values and the last two terms, which are coprime and greater than one. -/
structure State where
  used : Finset ℕ
  older : ℕ
  current : ℕ
  older_gt_one : 1 < older
  current_gt_one : 1 < current
  current_mem : current ∈ used
  coprime : Nat.Coprime older current

/-- An unused value sharing a factor with the older term and coprime to the current one. -/
def Admissible (s : State) (m : ℕ) : Prop :=
  1 < m ∧ m ∉ s.used ∧ 1 < Nat.gcd m s.older ∧ Nat.Coprime m s.current

instance (s : State) (m : ℕ) : Decidable (Admissible s m) :=
  inferInstanceAs (Decidable
    (1 < m ∧ m ∉ s.used ∧ 1 < Nat.gcd m s.older ∧ Nat.Coprime m s.current))

/-- Bertrand's postulate bounds a fresh prime multiplier of the older term. -/
def searchBound (s : State) : ℕ :=
  2 * s.older * (s.used.sup id + 1)

/-- The admissible values at most the search bound. -/
def candidates (s : State) : Finset ℕ :=
  (Finset.range (searchBound s + 1)).filter (Admissible s)

/-- A sufficiently large prime multiplier gives a fresh admissible value within the bound. -/
@[category API, AMS 11]
theorem candidates_nonempty (s : State) : (candidates s).Nonempty := by
  obtain ⟨p, hp, hpgt, hple⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (s.used.sup id + 1) (by omega)
  have hold := s.older_gt_one
  have hcur := s.current_gt_one
  have hcurle : s.current ≤ s.used.sup id := Finset.le_sup (f := id) s.current_mem
  have hpcoprime : Nat.Coprime p s.current :=
    hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have hbound : s.older * p ≤ searchBound s := by
    simpa [searchBound, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_le_mul_left s.older hple
  have hp_le_mul : p ≤ s.older * p := by
    simpa using Nat.mul_le_mul_right p (by omega : 1 ≤ s.older)
  have hlarge : s.used.sup id < s.older * p := by omega
  have hfresh : s.older * p ∉ s.used := by
    intro hmem
    have hle : s.older * p ≤ s.used.sup id := Finset.le_sup (f := id) hmem
    omega
  refine ⟨s.older * p, Finset.mem_filter.mpr ⟨?_, ?_, hfresh, ?_, ?_⟩⟩
  · exact Finset.mem_range.mpr (by omega)
  · have hpone := hp.one_lt
    omega
  · simpa [Nat.mul_comm] using hold
  · exact s.coprime.mul_left hpcoprime

/-- The least unused value satisfying the two gcd conditions. -/
def next (s : State) : ℕ :=
  (candidates s).min' (candidates_nonempty s)

/-- The next value is unused and has exactly the required coprimality properties. -/
@[category API, AMS 11]
theorem next_admissible (s : State) : Admissible s (next s) :=
  (Finset.mem_filter.mp (Finset.min'_mem (candidates s) (candidates_nonempty s))).2

/-- The finite search yields the globally least admissible positive integer. -/
@[category API, AMS 11]
theorem next_le (s : State) {m : ℕ} (hm : Admissible s m) : next s ≤ m := by
  by_cases hbound : m ≤ searchBound s
  · exact Finset.min'_le _ _
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hm⟩)
  · have hmem := Finset.min'_mem (candidates s) (candidates_nonempty s)
    have hle := Finset.mem_range.mp (Finset.mem_filter.mp hmem).1
    change next s < searchBound s + 1 at hle
    omega

/-- Advance the two-term history after selecting the least admissible value. -/
def step (s : State) : State where
  used := insert (next s) s.used
  older := s.current
  current := next s
  older_gt_one := s.current_gt_one
  current_gt_one := (next_admissible s).1
  current_mem := Finset.mem_insert_self _ _
  coprime := (next_admissible s).2.2.2.symm

/-- The state after the first $n+3$ official terms. -/
def state : ℕ → State
  | 0 => ⟨{1, 2, 3}, 2, 3, by decide, by decide, by decide, by decide⟩
  | n + 1 => step (state n)

/-- The Yellowstone permutation with its official one-based indexing. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 => (state n).current

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 4 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 9 := by decide

@[category test, AMS 11]
theorem a_6 : a 6 = 8 := by decide

set_option maxRecDepth 8192 in
@[category test, AMS 11]
theorem a_9 : a 9 = 5 := by decide

set_option maxRecDepth 8192 in
@[category test, AMS 11]
theorem a_12 : a 12 = 12 := by decide

/-- The number of official indices through $n$ whose term is at or below the diagonal. -/
def belowDiagonalCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => a k ≤ k)).card

@[category test, AMS 11]
theorem below_diagonal_count_zero : belowDiagonalCount 0 = 0 := by decide

@[category test, AMS 11]
theorem below_diagonal_count_five : belowDiagonalCount 5 = 4 := by decide

@[category test, AMS 11]
theorem fifth_term_not_below_diagonal : ¬a 5 ≤ 5 := by rw [a_5]; decide

@[category test, AMS 11]
theorem fourth_term_on_diagonal : a 4 ≤ 4 := by rw [a_4]

/-- The state transition preserves consecutive coprimality and uses a new value. -/
@[category API, AMS 11]
theorem step_invariants (s : State) :
    Nat.Coprime (step s).older (step s).current ∧
      (step s).current ∉ s.used ∧ 1 < Nat.gcd (step s).current s.older := by
  exact ⟨(step s).coprime, (next_admissible s).2.1, (next_admissible s).2.2.1⟩

/-- OEIS Conjecture 6 states:
"6. The value of |{k=1,..,n: a(k)<=k}|/n tends to 1/2."
Thus $\#\{1\le k\le n : a(k)\le k\}/n \to 1/2$, including fixed points. -/
@[category research open, AMS 11]
theorem below_diagonal_density :
    Filter.Tendsto (fun n : ℕ => (belowDiagonalCount n : ℝ) / (n : ℝ))
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
  sorry

end OeisA98550
