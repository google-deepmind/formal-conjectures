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
# Periodic Golay pairs of length 106

A periodic Golay pair consists of two finite $\{\pm 1\}$-sequences whose periodic
autocorrelations sum to zero at every nontrivial cyclic shift. Periodic autocorrelation is
invariant under replacing a shift $s$ by $-s$, so it is enough to check
$1 \le s \le \lfloor v/2\rfloor$. This is the half-range convention used in the cited paper.
The smallest length for which the existence of such a pair is currently undecided is $106$.

*References:*
- T. Lumsden, I. Kotsireas, and C. Bright,
  [New Results on Periodic Golay Pairs](https://arxiv.org/abs/2408.15611), 2025.
-/

@[expose] public section

namespace Arxiv.«2408.15611»

/-- A binary sequence of length $v$, represented as a function into the subtype $\{\pm 1\}$. -/
abbrev BinarySequence (v : ℕ) := Fin v → {x : ℤ // x = 1 ∨ x = -1}

/-- The periodic autocorrelation
$\operatorname{PAF}(A,s)=\sum_{k=0}^{v-1}a_k a_{k+s}$, with indices taken modulo $v$. -/
def periodicAutocorrelation {v : ℕ} (A : BinarySequence v) (s : Fin v) : ℤ :=
  ∑ k : Fin v, (A k).1 * (A (k + s)).1

/-- Periodic autocorrelation is unchanged when a cyclic shift is reversed. -/
@[category API, AMS 5 11 68 94]
theorem periodic_autocorrelation_neg {v : ℕ} [NeZero v]
    (A : BinarySequence v) (s : Fin v) :
    periodicAutocorrelation A (-s) = periodicAutocorrelation A s := by
  symm
  unfold periodicAutocorrelation
  calc
    ∑ k : Fin v, (A k).1 * (A (k + s)).1 =
        ∑ j : Fin v, (A (j + -s)).1 * (A j).1 := by
      apply Fintype.sum_equiv (Equiv.addRight s)
      intro k
      simp [add_assoc]
    _ = ∑ j : Fin v, (A j).1 * (A (j + -s)).1 := by
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _

/-- Two binary sequences form a periodic Golay pair when their periodic autocorrelations sum to
zero at every nonzero cyclic shift. The cited paper states the equivalent half-range condition;
see `is_periodic_golay_pair_iff_half_range`. -/
def IsPeriodicGolayPair {v : ℕ} (A B : BinarySequence v) : Prop :=
  ∀ s : Fin v, s.val ≠ 0 →
    periodicAutocorrelation A s + periodicAutocorrelation B s = 0

/-- At length zero there are no cyclic shifts to check. -/
@[category test, AMS 5 11 68 94]
theorem is_periodic_golay_pair_length_zero (A B : BinarySequence 0) :
    IsPeriodicGolayPair A B := by
  intro s
  exact Fin.elim0 s

/-- At length one the only shift is zero, which the predicate excludes. -/
@[category test, AMS 5 11 68 94]
theorem is_periodic_golay_pair_length_one (A B : BinarySequence 1) :
    IsPeriodicGolayPair A B := by
  intro s hs
  fin_cases s
  exact (hs rfl).elim

/-- For positive length, checking every nonzero shift is equivalent to checking only the shifts
through $\lfloor v/2\rfloor$, as in the cited paper. -/
@[category API, AMS 5 11 68 94]
theorem is_periodic_golay_pair_iff_half_range {v : ℕ} (hv : 0 < v)
    (A B : BinarySequence v) :
    IsPeriodicGolayPair A B ↔
      ∀ s : Fin v, s.val ≠ 0 → s.val ≤ v / 2 →
        periodicAutocorrelation A s + periodicAutocorrelation B s = 0 := by
  let : NeZero v := ⟨Nat.ne_of_gt hv⟩
  constructor
  · intro h s hs _
    exact h s hs
  · intro h s hs
    by_cases hhalf : s.val ≤ v / 2
    · exact h s hs hhalf
    · have hsne : s ≠ 0 := Fin.val_ne_zero_iff.mp hs
      have hnegne : (-s : Fin v) ≠ 0 := neg_ne_zero.mpr hsne
      have hnegVal : (-s : Fin v).val ≠ 0 :=
        Fin.val_ne_zero_iff.mpr hnegne
      have hnegHalf : (-s : Fin v).val ≤ v / 2 := by
        rw [Fin.val_neg, if_neg hsne]
        omega
      have hzero := h (-s) hnegVal hnegHalf
      rw [periodic_autocorrelation_neg A s,
        periodic_autocorrelation_neg B s] at hzero
      exact hzero

/-- At length four, shifts one and three are mirror shifts. -/
@[category test, AMS 5 11 68 94]
theorem periodic_autocorrelation_length_four_mirror
    (A : BinarySequence 4) :
    periodicAutocorrelation A 3 = periodicAutocorrelation A 1 := by
  have hshift : -(1 : Fin 4) = 3 := by decide
  simpa only [hshift] using periodic_autocorrelation_neg A (1 : Fin 4)

/-- The constant binary sequence $(1,1)$ of length two. -/
def lengthTwoA : BinarySequence 2 :=
  ![⟨1, Or.inl rfl⟩, ⟨1, Or.inl rfl⟩]

/-- The binary sequence $(1,-1)$ of length two. -/
def lengthTwoB : BinarySequence 2 :=
  ![⟨1, Or.inl rfl⟩, ⟨-1, Or.inr rfl⟩]

@[category test, AMS 5 11 68 94]
theorem periodic_autocorrelation_length_two_a_one :
    periodicAutocorrelation lengthTwoA 1 = 2 := by
  norm_num [periodicAutocorrelation, lengthTwoA, Fin.sum_univ_two, Fin.add_def]

@[category test, AMS 5 11 68 94]
theorem periodic_autocorrelation_length_two_b_one :
    periodicAutocorrelation lengthTwoB 1 = -2 := by
  norm_num [periodicAutocorrelation, lengthTwoB, Fin.sum_univ_two, Fin.add_def]

/-- Two constant length-two sequences do not cancel their nonzero-shift correlations. -/
@[category test, AMS 5 11 68 94]
theorem not_is_periodic_golay_pair_length_two_a_a :
    ¬ IsPeriodicGolayPair lengthTwoA lengthTwoA := by
  intro h
  have hsum := h (1 : Fin 2) (by decide)
  norm_num [periodic_autocorrelation_length_two_a_one] at hsum

@[category test, AMS 5 11 68 94]
theorem is_periodic_golay_pair_length_two :
    IsPeriodicGolayPair lengthTwoA lengthTwoB := by
  intro s hs
  fin_cases s
  · exact (hs rfl).elim
  · norm_num [periodicAutocorrelation, lengthTwoA, lengthTwoB, Fin.sum_univ_two, Fin.add_def]

/--
Does a periodic Golay pair of length $106$ exist? The cited paper identifies $106$ as the smallest
length for which existence is undecided. At this length, the displayed paper definition checks
shifts $1,\ldots,53$; `is_periodic_golay_pair_iff_half_range` proves that the all-nonzero-shifts
predicate used here is equivalent.

*Reference:* [New Results on Periodic Golay Pairs](https://arxiv.org/abs/2408.15611)
-/
@[category research open, AMS 5 11 68 94]
theorem exists_periodic_golay_pair_106 :
    answer(sorry) ↔ ∃ A B : BinarySequence 106, IsPeriodicGolayPair A B := by
  sorry

end Arxiv.«2408.15611»
