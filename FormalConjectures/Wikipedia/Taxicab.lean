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

import FormalConjectures.Util.ProblemImports

/-!
# Taxicab numbers

A "taxicab number" for natural numbers k, m, n is the smallest number x that can be expressed as a sum of m positive k-th powers in at least n distinct ways. The most famous taxicab number is
1729 = 1³ + 12³ = 9³ + 10³, also known as the Hardy–Ramanujan number.

However, Taxicab(5, 2, n) is not known for any n ≥ 2:
No positive integer is known that can be written as the sum of two 5th powers in more than one way, and it is not known whether such a number exists.

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Taxicab_number)
 - [Generalized taxicab number](https://en.wikipedia.org/wiki/Generalized_taxicab_number)
-/

namespace Taxicab

/-- Predicates for non-empty list with all non-zero elements -/
def is_nonempty_nonzero (L : List ℕ) : Prop := L ≠ [] ∧ 0 ∉ L

/-- The sum of the k-th powers of the elements of a list.
-/
def sum_of_kth_powers (k : ℕ) (L : List ℕ) : ℕ :=
  (L.map (· ^ k)).sum

/-- x is a candidate for being a taxicab number for k, m, n if there exists a (finite) set of at least n distinct, pairwise disjoint, non-empty, non-zero lists of length m, such that the sum of the k-th powers of the elements of each list is x. The disjointness condition ensures that the representations do not share any common terms.
-/
def is_possible_taxicab_for (k m n : ℕ) (x : ℕ) : Prop :=
  ∃ (S : Finset (List ℕ)),
  S.card ≥ n ∧
  ∀ L ∈ S, ∀ M ∈ S, L ≠ M → List.Disjoint L M ∧
  (∀ L ∈  S, L.length = m ∧ is_nonempty_nonzero L ∧ sum_of_kth_powers k L = x)

/-- 1729 is a possible taxicab number for k=3, m=2, n=2.
-/
@[category test, AMS 11]
theorem taxicab_1729_is_possible : is_possible_taxicab_for 3 2 2 1729 := by
  use {{1, 12}, {9, 10}}
  simp [List.Disjoint, sum_of_kth_powers];
  simp [is_nonempty_nonzero]
  simp +decide


/-- The set of all possible taxicab numbers for given k, m, n.
-/
def set_of_possible_taxicab_numbers_for (k m n : ℕ) : Set ℕ := { x : ℕ | is_possible_taxicab_for k m n x }

/-- x is a taxicab number if it is the smallest number that can be expressed as a sum of m positive k-th powers in at least n distinct ways.
-/
def is_taxicab (k m n : ℕ) (x : ℕ) : Prop :=
  IsLeast (set_of_possible_taxicab_numbers_for k m n) x

@[category test, AMS 11]
theorem taxicab_possible_4 : is_possible_taxicab_for 1 2 2 4 := by
  use {[1, 3], [2, 2]};
  simp [List.Disjoint, sum_of_kth_powers];
  simp [is_nonempty_nonzero]

/-- Using Aristotle (Harmonic) we get a compact proof that 4 is the taxicab number for k=1, m=2, n=2. -/
@[category test, AMS 11]
theorem taxicab_4 : is_taxicab 1 2 2 4 := by
  constructor;
  · exact taxicab_possible_4;
  · rintro x ⟨ S, hS₁, hS₂ ⟩;
    obtain ⟨ s, hs, t, ht, hst ⟩ := Finset.one_lt_card.mp hS₁;
    have := hS₂ s hs t ht hst;
    rcases this with ⟨ h₁, h₂ ⟩ ;
    specialize h₂ s hs;
    rcases s with ( _ | ⟨ a, _ | ⟨ b, _ | s ⟩ ⟩ ) <;> simp_all +arith +decide;
    rcases t with ( _ | ⟨ c, _ | ⟨ d, _ | t ⟩ ⟩ ) <;> simp_all +arith +decide [ is_nonempty_nonzero ];
    · grind;
    · have := hS₂ _ ht _ hs; simp_all +decide ;
      grind;
    · have := hS₂ _ hs _ ht; simp_all +decide [ List.Disjoint ] ;
      have := this.2 _ hs; have := this.2.2; simp_all +arith +decide [ sum_of_kth_powers ] ;
      grind;
    · have := hS₂ _ hs _ ht; simp_all +decide [ List.Disjoint ] ;
      grind +ring

/-- Taxicab number for k=5, m=2, n=2 is not-known. Whether such a number exists is also not known. -/
@[category research open, AMS 11]
theorem taxicab_522 : answer(sorry) ↔ ∃ x : ℕ, is_taxicab 5 2 2 x := by
  sorry

end Taxicab
