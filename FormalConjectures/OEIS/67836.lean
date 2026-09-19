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
# Euclid–Fortunate prime coverage

OEIS A067836 starts with $2$. Each later term is the gap from the product of all previous terms to
the least prime strictly greater than that product plus one.

*References:*
- [OEIS A067836](https://oeis.org/A067836)
-/

namespace OeisA67836

/-- The finite set in which the least prime strictly above `n` is sought. -/
def primeCandidates (n : ℕ) : Finset ℕ :=
  (Finset.Icc (n + 1) (2 * (n + 1))).filter Nat.Prime

/-- Bertrand's postulate makes the finite prime-candidate set nonempty. -/
@[category API, AMS 11]
lemma primeCandidates_nonempty (n : ℕ) : (primeCandidates n).Nonempty := by
  obtain ⟨p, hp, hnp, hp_le⟩ := Nat.bertrand (n + 1) (by omega)
  refine ⟨p, ?_⟩
  simp only [primeCandidates, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by omega, hp_le⟩, hp⟩

/-- The least prime strictly greater than `n`, found in the Bertrand interval. -/
def leastPrimeAbove (n : ℕ) : ℕ :=
  (primeCandidates n).min' (primeCandidates_nonempty n)

/-- The chosen number is strictly above the bound and is prime. -/
@[category API, AMS 11]
lemma leastPrimeAbove_spec (n : ℕ) :
    n < leastPrimeAbove n ∧ (leastPrimeAbove n).Prime := by
  have hmem := Finset.min'_mem (primeCandidates n) (primeCandidates_nonempty n)
  simp only [primeCandidates, Finset.mem_filter, Finset.mem_Icc] at hmem
  have hbound : n < leastPrimeAbove n := by
    simpa only [leastPrimeAbove, primeCandidates, Nat.lt_iff_add_one_le] using hmem.1.1
  have hprime : (leastPrimeAbove n).Prime := by
    simpa only [leastPrimeAbove, primeCandidates] using hmem.2
  exact ⟨hbound, hprime⟩

/-- The least prime above `n` is no larger than any other prime above `n`. -/
@[category API, AMS 11]
lemma leastPrimeAbove_le (n p : ℕ) (hnp : n < p) (hp : p.Prime) :
    leastPrimeAbove n ≤ p := by
  by_cases hp_bound : p ≤ 2 * (n + 1)
  · have hp_mem : p ∈ primeCandidates n := by
      simp only [primeCandidates, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, hp_bound⟩, hp⟩
    exact Finset.min'_le _ _ hp_mem
  · have hmem := Finset.min'_mem (primeCandidates n) (primeCandidates_nonempty n)
    simp only [primeCandidates, Finset.mem_filter, Finset.mem_Icc] at hmem
    have hbound : leastPrimeAbove n ≤ 2 * (n + 1) := by
      simpa only [leastPrimeAbove, primeCandidates] using hmem.1.2
    omega

/-- No number strictly between `n` and `leastPrimeAbove n` is prime. -/
@[category API, AMS 11]
lemma not_prime_of_lt_leastPrimeAbove (n p : ℕ) (hnp : n < p)
    (hp : p < leastPrimeAbove n) : ¬ p.Prime := by
  intro hp_prime
  have := leastPrimeAbove_le n p hnp hp_prime
  omega

/-- A convenient criterion for computing the least prime above a concrete bound. -/
@[category API, AMS 11]
lemma leastPrimeAbove_eq (n p : ℕ) (hnp : n < p) (hp : p.Prime)
    (hmin : ∀ q, n < q → q < p → ¬ q.Prime) : leastPrimeAbove n = p := by
  apply Nat.le_antisymm (leastPrimeAbove_le n p hnp hp)
  by_contra h
  have hlt : leastPrimeAbove n < p := by omega
  exact hmin (leastPrimeAbove n) (leastPrimeAbove_spec n).1 hlt (leastPrimeAbove_spec n).2

/-- The recursive state records the latest term and the product of all official terms so far. -/
structure State where
  term : ℕ
  product : ℕ

/-- The state after `n` official terms, with the empty state initialized by term and product one. -/
def state : ℕ → State
  | 0 => ⟨1, 1⟩
  | n + 1 =>
      let previous := state n
      let next := leastPrimeAbove (previous.product + 1) - previous.product
      ⟨next, previous.product * next⟩

/-- OEIS A067836, with the convenience value `a 0 = 1` preceding its official first term. -/
def a (n : ℕ) : ℕ :=
  (state n).term

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  decide

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  decide

@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by
  decide

@[category test, AMS 11]
theorem a_4 : a 4 = 7 := by
  decide

set_option maxRecDepth 10000 in
@[category test, AMS 11]
theorem a_5 : a 5 = 13 := by
  decide

/-- [OEIS A067836](https://oeis.org/A067836) asks: "Do all primes occur in the sequence?" -/
@[category research open, AMS 11]
theorem conjecture :
    answer(sorry) ↔ ∀ p, p.Prime → ∃ n ≥ 1, a n = p := by
  sorry

end OeisA67836
