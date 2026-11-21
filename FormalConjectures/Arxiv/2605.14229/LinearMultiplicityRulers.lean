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
# Linear-multiplicity rulers

An LM ruler is a finite set of integer marks in which a positive difference $d$ occurs at most
$d-1$ times. Its diameter is at least the sum of the first $n-1$ entries of
$2,3,3,4,4,4,\ldots$, where $n$ is the number of marks. The open question asks whether this
integer lower bound is attained for every positive $n$.

*References:*
* A. Gupta and K. O'Bryant,
  [Optimal Diameters of High Multiplicity $g$-Golomb Rulers](https://arxiv.org/abs/2605.14229),
  version 2, Sections 5.1 and 7, Problem 7.
* [OEIS A392517](https://oeis.org/A392517).
-/

@[expose] public section

namespace Arxiv.«2605.14229»

/-- The number of representations of $d$ as a positive difference of marks of $A$. -/
def differenceCount (A : Finset ℕ) (d : ℕ) : ℕ :=
  (A.filter fun x => x + d ∈ A).card

/-- Every positive difference $d$ occurs at most $d-1$ times. -/
def IsLMRuler (A : Finset ℕ) : Prop :=
  ∀ d ∈ Finset.Icc 1 (A.sup id), differenceCount A d ≤ d - 1

instance (A : Finset ℕ) : Decidable (IsLMRuler A) := by
  unfold IsLMRuler
  infer_instance

/-- Sum the first $n-1$ entries in the gap list $2,3,3,4,4,4,\ldots$. -/
def gapLowerBound (n : ℕ) : ℕ :=
  (((List.range n).flatMap fun i => List.replicate (i + 1) (i + 2)).take (n - 1)).sum

/-- A difference larger than the maximum mark has no representation. -/
@[category API, AMS 5 11 94]
theorem difference_count_eq_zero_of_max_lt (A : Finset ℕ) (d : ℕ)
    (h : A.sup id < d) : differenceCount A d = 0 := by
  rw [differenceCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx hxd
  have hmax : x + d ≤ A.sup id := Finset.le_sup (f := id) hxd
  omega

/-- The finite check covers every positive difference, including those beyond the ruler. -/
@[category API, AMS 5 11 94]
theorem is_lm_ruler_iff (A : Finset ℕ) :
    IsLMRuler A ↔ ∀ d : ℕ, 0 < d → differenceCount A d ≤ d - 1 := by
  constructor
  · intro h d hd
    by_cases hmax : d ≤ A.sup id
    · exact h d (Finset.mem_Icc.mpr ⟨by omega, hmax⟩)
    · rw [difference_count_eq_zero_of_max_lt A d (by omega)]
      exact Nat.zero_le _
  · intro h d hd
    have hdpos : 0 < d := by
      have := (Finset.mem_Icc.mp hd).1
      omega
    exact h d hdpos

/-- The zero difference counts every mark and is excluded from the LM restriction. -/
@[category API, AMS 5 11 94]
theorem difference_count_zero (A : Finset ℕ) : differenceCount A 0 = A.card := by
  simp [differenceCount]

@[category test, AMS 5 11 94]
theorem gap_lower_bound_one : gapLowerBound 1 = 0 := by decide

@[category test, AMS 5 11 94]
theorem gap_lower_bound_two : gapLowerBound 2 = 2 := by decide

@[category test, AMS 5 11 94]
theorem gap_lower_bound_three : gapLowerBound 3 = 5 := by decide

@[category test, AMS 5 11 94]
theorem gap_lower_bound_four : gapLowerBound 4 = 8 := by decide

@[category test, AMS 5 11 94]
theorem gap_lower_bound_five : gapLowerBound 5 = 12 := by decide

@[category test, AMS 5 11 94]
theorem gap_lower_bound_six : gapLowerBound 6 = 16 := by decide

/-- The first six displayed optimal rulers satisfy the LM condition. -/
@[category test, AMS 5 11 94]
theorem small_lm_rulers :
    IsLMRuler {0} ∧ IsLMRuler {0, 2} ∧ IsLMRuler {0, 2, 5} ∧
      IsLMRuler {0, 2, 5, 8} ∧ IsLMRuler {0, 2, 5, 8, 12} ∧
      IsLMRuler {0, 2, 5, 8, 12, 16} := by
  decide

/-- Consecutive marks violate the zero capacity for distance one. -/
@[category test, AMS 5 11 94]
theorem adjacent_marks_not_lm : ¬ IsLMRuler {0, 1} := by
  decide

/-- Distance two may occur only once. -/
@[category test, AMS 5 11 94]
theorem repeated_gap_two_not_lm : ¬ IsLMRuler {0, 2, 4} := by
  decide

/-- The empty ruler satisfies the auxiliary property, but the question requires positive size. -/
@[category test, AMS 5 11 94]
theorem empty_lm_ruler : IsLMRuler ∅ := by
  decide

/-- The integer gap bound at eleven marks is forty. -/
@[category test, AMS 5 11 94]
theorem gap_lower_bound_eleven : gapLowerBound 11 = 40 := by
  decide

/-- A ruler attaining forty uses a different initial segment from the greedy mark construction. -/
@[category test, AMS 5 11 94]
theorem eleven_mark_witness :
    let A : Finset ℕ := {0, 2, 6, 9, 12, 16, 20, 25, 30, 35, 40}
    0 ∈ A ∧ A.card = 11 ∧ IsLMRuler A ∧ A.sup id = gapLowerBound 11 := by
  decide

/--
Is the integer adjacent-gap lower bound for an LM ruler attained for every positive number
of marks? The rulers are translated so that their least mark is zero.
-/
@[category research open, question, AMS 5 11 94]
theorem lm_diameter_attains_gap_bound :
    ∀ n : ℕ, 1 ≤ n → ∃ A : Finset ℕ,
      0 ∈ A ∧ A.card = n ∧ IsLMRuler A ∧ A.sup id = gapLowerBound n := by
  sorry

end Arxiv.«2605.14229»
