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
# A prime after deleting one reduced residue

For a composite integer $k$, sum all the integers from $1$ to $k-1$ that are coprime to $k$,
except for one chosen term. Count the choices that give a prime sum. OEIS A354846 gives the
least composite $k$ with exactly $n$ such choices, or $-1$ if there is no such $k$.

*References:*
- [OEIS A354846](https://oeis.org/A354846)
-/

@[expose] public section

namespace OeisA354846

open scoped BigOperators

/-- The integers $r$ with $1\le r<k$ that are coprime to $k$. -/
def residues (k : ℕ) : Finset ℕ :=
  (Finset.Ico 1 k).filter fun r => r.Coprime k

/-- The number of prime sums obtained by deleting one reduced residue. -/
def primeSumCount (k : ℕ) : ℕ :=
  ((residues k).filter fun r => (∑ t ∈ (residues k).erase r, t).Prime).card

/-- The least composite $k$ with exactly $n$ prime sums, or $-1$ if none exists. -/
noncomputable def a (n : ℕ) : ℤ := by
  classical
  exact if h : ∃ k, Nat.Composite k ∧ primeSumCount k = n then (Nat.find h : ℤ) else -1

/-- A witness and finite minimality determine an official term. -/
@[category API, AMS 11]
theorem a_eq_of_least {n k : ℕ} (hk : Nat.Composite k ∧ primeSumCount k = n)
    (hmin : ∀ j < k, ¬ (Nat.Composite j ∧ primeSumCount j = n)) : a n = k := by
  classical
  have hex : ∃ j, Nat.Composite j ∧ primeSumCount j = n := ⟨k, hk⟩
  have hfind : Nat.find hex = k := (Nat.find_eq_iff hex).mpr ⟨hk, hmin⟩
  simp only [a, dif_pos hex, hfind]

@[category test, AMS 11]
theorem a_1 : a 1 = 4 := by
  apply a_eq_of_least (n := 1) (k := 4) (by decide)
  intro j hj
  interval_cases j <;> decide

@[category test, AMS 11]
theorem a_2 : a 2 = 8 := by
  apply a_eq_of_least (n := 2) (k := 8) (by decide)
  intro j hj
  interval_cases j <;> decide

@[category test, AMS 11]
theorem a_3 : a 3 = 15 := by
  apply a_eq_of_least (n := 3) (k := 15) (by decide)
  intro j hj
  interval_cases j <;> decide

@[category test, AMS 11]
theorem a_4 : a 4 = 10 := by
  apply a_eq_of_least (n := 4) (k := 10) (by decide)
  intro j hj
  interval_cases j <;> decide

@[category test, AMS 11]
theorem a_5 : a 5 = 18 := by
  apply a_eq_of_least (n := 5) (k := 18) (by decide)
  intro j hj
  interval_cases j <;> decide

@[category test, AMS 11]
theorem residues_four : residues 4 = {1, 3} := by decide

@[category test, AMS 11]
theorem prime_sums_fifteen : primeSumCount 15 = 3 := by decide

@[category test, AMS 11]
theorem prime_sum_count_zero : primeSumCount 0 = 0 := by decide

@[category test, AMS 11]
theorem prime_sum_count_one : primeSumCount 1 = 0 := by decide

@[category test, AMS 11]
theorem prime_sum_count_two : primeSumCount 2 = 0 := by decide

/-- The missing-value branch uses the source's sentinel $-1$. -/
@[category API, AMS 11]
theorem a_eq_neg_one {n : ℕ} (h : ¬ ∃ k, Nat.Composite k ∧ primeSumCount k = n) :
    a n = -1 := by
  classical
  simp [a, h]

/-- The number of prime sums cannot exceed the number of reduced residues. -/
@[category API, AMS 11]
theorem prime_sum_count_le_card (k : ℕ) : primeSumCount k ≤ (residues k).card :=
  Finset.card_filter_le _ _

/-- "Conjecture: for every composite $k$ there is at least one such prime." -/
@[category research open, AMS 11]
theorem prime_after_deleting_reduced_residue :
    ∀ k : ℕ, Nat.Composite k → 0 < primeSumCount k := by
  sorry

end OeisA354846
