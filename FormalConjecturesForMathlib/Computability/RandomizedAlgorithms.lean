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

public import FormalConjecturesForMathlib.Computability.Complexity
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Rat

/-!
# Polynomial-time randomized decision algorithms

A deterministic TM2 machine receives the input and a uniformly chosen string of
polynomially many independent random bits. Its time bound applies to every pair,
not just on average. Exact rational probabilities count all coin strings.

The error conventions follow Vadhan, *Pseudorandomness*, §2.2, Definitions 2.9
and 2.13. ZPP uses the equivalent intersection characterization in Fact 2.16,
rather than introducing an expected-time machine model:
https://people.seas.harvard.edu/~salil/pseudorandomness/pseudorandomness-published-Dec12.pdf.
-/

@[expose] public section

namespace ComplexityTheory

namespace RandomCoins

/-- Number of accepting strings among all strings of exactly n bits. -/
def count (n : ℕ) (test : List Bool → Bool) : ℕ :=
  (Finset.univ.filter fun r : Fin n → Bool => test (List.ofFn r) = true).card

/-- Exact acceptance probability for n independent unbiased random bits. -/
def probability (n : ℕ) (test : List Bool → Bool) : ℚ :=
  (count n test : ℚ) / (2 : ℚ) ^ n

@[simp]
theorem count_false (n : ℕ) : count n (fun _ => false) = 0 := by
  simp [count]

@[simp]
theorem count_true (n : ℕ) : count n (fun _ => true) = 2 ^ n := by
  simp [count]

theorem count_le (n : ℕ) (test : List Bool → Bool) : count n test ≤ 2 ^ n := by
  simpa [count] using
    Finset.card_filter_le (Finset.univ : Finset (Fin n → Bool))
      (fun r => test (List.ofFn r) = true)

@[simp]
theorem probability_false (n : ℕ) : probability n (fun _ => false) = 0 := by
  simp [probability]

@[simp]
theorem probability_true (n : ℕ) : probability n (fun _ => true) = 1 := by
  simp [probability]

theorem probability_nonneg (n : ℕ) (test : List Bool → Bool) :
    0 ≤ probability n test := by
  exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (pow_pos (by decide) _))

theorem probability_le_one (n : ℕ) (test : List Bool → Bool) :
    probability n test ≤ 1 := by
  apply (div_le_one (pow_pos (by decide : (0 : ℚ) < 2) n)).mpr
  exact_mod_cast count_le n test

/-- Acceptance depends only on the test's behavior on strings of the sampled length. -/
theorem probability_congr (n : ℕ) {f g : List Bool → Bool}
    (h : ∀ r, r.length = n → f r = g r) :
    probability n f = probability n g := by
  unfold probability count
  congr 2
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro r _
  rw [h (List.ofFn r) List.length_ofFn]

end RandomCoins

/-- Two-sided error at most 1/3, on every input separately. -/
def BoundedError (p : Polynomial ℕ) (A : List Bool × List Bool → Bool)
    (L : DecisionProblem) : Prop :=
  ∀ x, (2 / 3 : ℚ) ≤ RandomCoins.probability (p.eval x.length)
    (fun r => A (x, r) == L x)

/-- No false positives and probability at least 1/2 of accepting each yes-instance. -/
def OneSidedError (p : Polynomial ℕ) (A : List Bool × List Bool → Bool)
    (L : DecisionProblem) : Prop :=
  ∀ x,
    (L x = true → (1 / 2 : ℚ) ≤
      RandomCoins.probability (p.eval x.length) (fun r => A (x, r))) ∧
    (L x = false → ∀ r, r.length = p.eval x.length → A (x, r) = false)

/-- Bounded-error probabilistic polynomial time with an actual TM2 verifier. -/
def BPP : Set DecisionProblem :=
  {L | ∃ p A, IsPolyTime A ∧ BoundedError p A L}

/-- One-sided-error randomized polynomial time with an actual TM2 verifier. -/
def RP : Set DecisionProblem :=
  {L | ∃ p A, IsPolyTime A ∧ OneSidedError p A L}

/-- Complements of RP languages. -/
def coRP : Set DecisionProblem :=
  {L | (fun x => !(L x)) ∈ RP}

/-- Zero-error polynomial time, using Vadhan's RP ∩ coRP characterization. -/
def ZPP : Set DecisionProblem := RP ∩ coRP

@[simp]
theorem mem_zpp (L : DecisionProblem) :
    L ∈ ZPP ↔ L ∈ RP ∧ (fun x => !(L x)) ∈ RP := Iff.rfl

theorem zpp_subset_rp : ZPP ⊆ RP := fun _ h => h.1

end ComplexityTheory
