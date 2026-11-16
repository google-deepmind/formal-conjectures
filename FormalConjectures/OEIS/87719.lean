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
# Conjectures associated with A087719

Define $\varsigma(n)$ the smallest prime factor of $n$ (`Nat.minFac`). Let $a_n$ be the least
number such that the count of numbers $k \le a_n$ with $k > \varsigma(k)^n$ exceeds the count
of numbers with $k \le \varsigma(k)^n$.

The conjecture states that $a_n = 3^n + 3 \cdot 2^n + 6$ for $n \ge 1$.

*References:*
- [A087719](https://oeis.org/A087719)
-/

@[expose] public section

namespace OeisA87719

open Nat

/-- Count of numbers k in {1, ..., m} where k > (minFac k)^n. -/
def countExceeding (n m : ℕ) : ℕ :=
  (Finset.Icc 1 m).filter (fun k => k > k.minFac ^ n) |>.card

/-- Count of numbers k in {1, ..., m} where k ≤ (minFac k)^n. -/
def countNotExceeding (n m : ℕ) : ℕ :=
  (Finset.Icc 1 m).filter (fun k => k ≤ k.minFac ^ n) |>.card

/-- There exists m such that countExceeding n m > countNotExceeding n m. -/
@[category textbook, AMS 11]
theorem a_exists (n : ℕ) : ∃ m, countExceeding n m > countNotExceeding n m := by
  -- Take `m = 6 * (3 ^ n + 1)`. A number `k > 3 ^ n` that is divisible by `2` or `3` exceeds
  -- `minFac k ^ n`. So a number that does not exceed is at most `3 ^ n` or coprime to `6`.
  set M := 3 ^ n + 1 with hM
  refine ⟨6 * M, ?_⟩
  have hpart : countExceeding n (6 * M) + countNotExceeding n (6 * M) = 6 * M := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 (6 * M))
      (fun k => k > k.minFac ^ n)
    simpa [countExceeding, countNotExceeding, not_lt] using this
  have hsub : (Finset.Icc 1 (6 * M)).filter (fun k => k ≤ k.minFac ^ n) ⊆
      Finset.Icc 1 (3 ^ n) ∪ ((Finset.range M).image (fun j => 6 * j + 1) ∪
        (Finset.range M).image (fun j => 6 * j + 5)) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1a, hk1b⟩ := Finset.mem_Icc.mp hk1
    by_cases hle : k ≤ 3 ^ n
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hk1a, hle⟩)
    · refine Finset.mem_union_right _ ?_
      have h23 := Nat.pow_le_pow_left (show 2 ≤ 3 by norm_num) n
      have h2 : ¬ 2 ∣ k := fun h => by
        have := Nat.pow_le_pow_left (Nat.minFac_le_of_dvd (le_refl 2) h) n
        omega
      have h3 : ¬ 3 ∣ k := fun h => by
        have := Nat.pow_le_pow_left (Nat.minFac_le_of_dvd (show 2 ≤ 3 by norm_num) h) n
        omega
      have hmod : k % 6 = 1 ∨ k % 6 = 5 := by omega
      rcases hmod with h | h
      · exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨k / 6, Finset.mem_range.mpr (by omega), by omega⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨k / 6, Finset.mem_range.mpr (by omega), by omega⟩)
  have hcard : countNotExceeding n (6 * M) ≤ 3 ^ n + (M + M) := by
    unfold countNotExceeding
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    refine Nat.add_le_add (by simp) ((Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_))
    · exact Finset.card_image_le.trans (by simp)
    · exact Finset.card_image_le.trans (by simp)
  omega

/-- The sequence a(n): least m such that countExceeding n m > countNotExceeding n m. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.find (a_exists n)

/-- a(1) = 15. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 15 := by
  rw [a, Nat.find_eq_iff]
  refine ⟨by decide +native, ?_⟩
  intro m hm
  interval_cases m <;> decide +native

/-- a(2) = 27. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 27 := by
  rw [a, Nat.find_eq_iff]
  refine ⟨by decide +native, ?_⟩
  intro m hm
  interval_cases m <;> decide +native

/-- a(3) = 57. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 57 := by
  rw [a, Nat.find_eq_iff]
  refine ⟨by decide +native, ?_⟩
  intro m hm
  interval_cases m <;> decide +native

/-- We have the following formula: $a(n) = 3^n + 3 * 2^n + 6$ for $n \geq 1$. -/
@[category textbook, AMS 11,
  formal_proof using formal_conjectures at
    "https://github.com/google-deepmind/formal-conjectures/blob/7a286754f623759d69a3dd18f482c53c1d70959b/FormalConjectures/OEIS/87719.lean#L640"]
theorem a_formula {n : ℕ} (hn : n ≥ 1) : a n = 3 ^ n + 3 * 2 ^ n + 6 := by
  sorry

end OeisA87719
