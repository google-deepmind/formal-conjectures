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
# Tripling until the seed's digits reappear

Starting with the least positive integer not used previously, repeatedly triple it and stop the
block at the first positive power whose decimal expansion contains the seed's digits. Then repeat
from the new least missing positive integer.

*References:*
- [A331631](https://oeis.org/A331631)
-/

@[expose] public section

namespace OeisA331631

/-- The decimal digits of `seed` occur contiguously in the decimal digits of `value`. -/
def ContainsSeed (seed value : ℕ) : Prop :=
  (Nat.digits 10 seed).IsInfix (Nat.digits 10 value)

@[category test, AMS 11]
theorem contains_seed_12_5123 : ContainsSeed 12 5123 := by
  norm_num [ContainsSeed, List.infix_cons_iff, List.prefix_cons_iff,
    Nat.digits_of_two_le_of_pos]

@[category test, AMS 11]
theorem not_contains_seed_12_5213 : ¬ContainsSeed 12 5213 := by
  norm_num [ContainsSeed, List.infix_cons_iff, List.prefix_cons_iff,
    Nat.digits_of_two_le_of_pos]
  decide

/-- `exponent` is the first positive tripling exponent whose value contains the seed. -/
def StopsAt (seed exponent : ℕ) : Prop :=
  0 < exponent ∧
    ContainsSeed seed (seed * 3 ^ exponent) ∧
    ∀ j, 0 < j → j < exponent → ¬ContainsSeed seed (seed * 3 ^ j)

@[category test, AMS 11]
theorem not_stops_at_1_0 : ¬StopsAt 1 0 := by
  simp [StopsAt]

/-- The complete block through its first successful positive tripling exponent. -/
def blockValues (seed exponent : ℕ) : List ℕ :=
  (List.range (exponent + 1)).map fun j ↦ seed * 3 ^ j

/-- A block includes its seed and every product through the stopping exponent. -/
@[category API, AMS 11]
theorem block_values_length (seed exponent : ℕ) :
    (blockValues seed exponent).length = exponent + 1 := by
  simp [blockValues]

/-- `value` is positive and has not occurred before index `start`. -/
def MissingBefore (a : ℕ → ℕ) (start value : ℕ) : Prop :=
  0 < value ∧ ∀ i < start, a i ≠ value

/-- `seed` is the least positive value missing before a block boundary. -/
def LeastMissingBefore (a : ℕ → ℕ) (start seed : ℕ) : Prop :=
  MissingBefore a start seed ∧
    ∀ value, MissingBefore a start value → seed ≤ value

/--
A total sequence follows the construction when explicit consecutive block boundaries and finite
first-stopping exponents witness every block.
-/
def FollowsRule (a : ℕ → ℕ) : Prop :=
  ∃ boundary stop : ℕ → ℕ,
    boundary 0 = 0 ∧
    ∀ blockIndex,
      let start := boundary blockIndex
      let seed := a start
      LeastMissingBefore a start seed ∧
        StopsAt seed (stop blockIndex) ∧
        (∀ j ≤ stop blockIndex, a (start + j) = seed * 3 ^ j) ∧
        boundary (blockIndex + 1) = start + stop blockIndex + 1

/-- `seed` is the least positive value absent from the finite history. -/
def LeastMissing (history : List ℕ) (seed : ℕ) : Prop :=
  0 < seed ∧ seed ∉ history ∧
    ∀ smaller ∈ Finset.Ico 1 seed, smaller ∈ history

/-- A finite history made by appending complete source-valid blocks. -/
inductive ValidBlockPrefix : List ℕ → Prop
  | nil : ValidBlockPrefix []
  | append {history : List ℕ} {seed exponent : ℕ}
      (valid : ValidBlockPrefix history)
      (least : LeastMissing history seed)
      (stops : StopsAt seed exponent) :
      ValidBlockPrefix (history ++ blockValues seed exponent)

/--
A value occurs at the official OEIS index $n\geq 1$ in a finite valid prefix.
The total sequences in `FollowsRule` use index $n-1$ for the same term.
-/
def TermAt (n value : ℕ) : Prop :=
  0 < n ∧ ∃ xs, ValidBlockPrefix xs ∧ xs[n - 1]? = some value

/-- Index zero is outside the official OEIS domain. -/
@[category test, AMS 11]
theorem not_term_at_zero (value : ℕ) : ¬TermAt 0 value := by
  simp [TermAt]

private def initialBlocks : List ℕ :=
  [1, 3, 9, 27, 81, 2, 6, 18, 54, 162, 4, 12, 36, 108, 324, 5, 15]

@[category API, AMS 11]
private theorem initialBlocks_valid : ValidBlockPrefix initialBlocks := by
  have h0 : ValidBlockPrefix [] := ValidBlockPrefix.nil
  have h1 : ValidBlockPrefix [1, 3, 9, 27, 81] := by
    have hblock : blockValues 1 4 = [1, 3, 9, 27, 81] := by decide
    simpa only [hblock, List.nil_append] using
      ValidBlockPrefix.append (seed := 1) (exponent := 4) h0
        (by norm_num [LeastMissing]) (by
          norm_num [StopsAt, ContainsSeed, List.infix_cons_iff, List.prefix_cons_iff,
            Nat.digits_of_two_le_of_pos]
          intro j hj hlt
          interval_cases j <;>
            norm_num [ContainsSeed, List.infix_cons_iff, List.prefix_cons_iff,
              Nat.digits_of_two_le_of_pos])
  have h2 : ValidBlockPrefix [1, 3, 9, 27, 81, 2, 6, 18, 54, 162] := by
    have hblock : blockValues 2 4 = [2, 6, 18, 54, 162] := by decide
    simpa only [hblock, List.cons_append, List.nil_append] using
      ValidBlockPrefix.append (seed := 2) (exponent := 4) h1
        (by
          norm_num [LeastMissing])
        (by
          norm_num [StopsAt, ContainsSeed, List.infix_cons_iff, List.prefix_cons_iff,
            Nat.digits_of_two_le_of_pos]
          intro j hj hlt
          interval_cases j <;>
            norm_num [ContainsSeed, List.infix_cons_iff, List.prefix_cons_iff,
              Nat.digits_of_two_le_of_pos])
  have h3 : ValidBlockPrefix [1, 3, 9, 27, 81, 2, 6, 18, 54, 162, 4, 12, 36, 108, 324] := by
    have hblock : blockValues 4 4 = [4, 12, 36, 108, 324] := by decide
    simpa only [hblock, List.cons_append, List.nil_append] using
      ValidBlockPrefix.append (seed := 4) (exponent := 4) h2
        (by
          norm_num [LeastMissing]
          intro smaller hsmall hlt
          interval_cases smaller <;> norm_num)
        (by
          norm_num [StopsAt, ContainsSeed, List.infix_cons_iff, List.prefix_cons_iff,
            Nat.digits_of_two_le_of_pos]
          intro j hj hlt
          interval_cases j <;>
            norm_num [ContainsSeed, List.infix_cons_iff, List.prefix_cons_iff,
              Nat.digits_of_two_le_of_pos])
  have h4 : ValidBlockPrefix initialBlocks := by
    have hblock : blockValues 5 1 = [5, 15] := by decide
    simpa only [initialBlocks, hblock, List.cons_append, List.nil_append] using
      ValidBlockPrefix.append (seed := 5) (exponent := 1) h3
        (by
          norm_num [LeastMissing]
          intro smaller hsmall hlt
          interval_cases smaller <;> norm_num)
        (by
          norm_num [StopsAt, ContainsSeed, List.infix_cons_iff, List.prefix_cons_iff,
            Nat.digits_of_two_le_of_pos]
          intro j hj hzero
          omega)
  exact h4

@[category test, AMS 11]
theorem a_1 : TermAt 1 1 := by
  exact ⟨by decide, initialBlocks, initialBlocks_valid, by decide⟩

@[category test, AMS 11]
theorem a_2 : TermAt 2 3 := by
  exact ⟨by decide, initialBlocks, initialBlocks_valid, by decide⟩

@[category test, AMS 11]
theorem a_3 : TermAt 3 9 := by
  exact ⟨by decide, initialBlocks, initialBlocks_valid, by decide⟩

@[category test, AMS 11]
theorem a_4 : TermAt 4 27 := by
  exact ⟨by decide, initialBlocks, initialBlocks_valid, by decide⟩

@[category test, AMS 11]
theorem a_5 : TermAt 5 81 := by
  exact ⟨by decide, initialBlocks, initialBlocks_valid, by decide⟩

@[category test, AMS 11]
theorem a_6 : TermAt 6 2 := by
  exact ⟨by decide, initialBlocks, initialBlocks_valid, by decide⟩

@[category test, AMS 11]
theorem a_7 : TermAt 7 6 := by
  exact ⟨by decide, initialBlocks, initialBlocks_valid, by decide⟩

@[category test, AMS 11]
theorem a_8 : TermAt 8 18 := by
  exact ⟨by decide, initialBlocks, initialBlocks_valid, by decide⟩

@[category test, AMS 11]
theorem a_9 : TermAt 9 54 := by
  exact ⟨by decide, initialBlocks, initialBlocks_valid, by decide⟩

@[category test, AMS 11]
theorem a_10 : TermAt 10 162 := by
  exact ⟨by decide, initialBlocks, initialBlocks_valid, by decide⟩

@[category test, AMS 11]
theorem a_11 : TermAt 11 4 := by
  exact ⟨by decide, initialBlocks, initialBlocks_valid, by decide⟩

@[category test, AMS 11]
theorem a_12 : TermAt 12 12 := by
  exact ⟨by decide, initialBlocks, initialBlocks_valid, by decide⟩

@[category test, AMS 11]
theorem a_13 : TermAt 13 36 := by
  exact ⟨by decide, initialBlocks, initialBlocks_valid, by decide⟩

@[category test, AMS 11]
theorem a_14 : TermAt 14 108 := by
  exact ⟨by decide, initialBlocks, initialBlocks_valid, by decide⟩

@[category test, AMS 11]
theorem a_15 : TermAt 15 324 := by
  exact ⟨by decide, initialBlocks, initialBlocks_valid, by decide⟩

@[category test, AMS 11]
theorem a_16 : TermAt 16 5 := by
  exact ⟨by decide, initialBlocks, initialBlocks_valid, by decide⟩

@[category test, AMS 11]
theorem a_17 : TermAt 17 15 := by
  exact ⟨by decide, initialBlocks, initialBlocks_valid, by decide⟩

/--
[OEIS A331631](https://oeis.org/A331631) states:
The sequence is conjectured to be a permutation of the positive integers
(see the Crossrefs section).
-/
@[category research open, AMS 11]
theorem conjecture :
    ∃ a : ℕ → ℕ, FollowsRule a ∧ Function.Injective a ∧
      ∀ k > 0, ∃ n, a n = k := by
  sorry

end OeisA331631
