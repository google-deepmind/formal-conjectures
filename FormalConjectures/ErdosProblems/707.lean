/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE/2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 707: Embedding Sidon Sets in Perfect Difference Sets

*Reference:* [erdosproblems.com/707](https://www.erdosproblems.com/707)

Let A ⊂ ℕ be a finite Sidon set. Is there some set B with A ⊆ B which is a perfect
difference set modulo p^2 + p + 1 for some prime p?

This problem is related to Erdős Problem 329 about the maximum density of Sidon sets.
If this conjecture is true, it would imply that the maximum density of Sidon sets is 1.
-/

open Function Set

/-- A finite set A is a Sidon set if all pairwise sums are distinct. -/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a b c d ∈ A, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A set B is a perfect difference set modulo n if every non-zero element
    of Z/nZ can be written as a difference of two elements of B in exactly one way. -/
def IsPerfectDifferenceSetModulo (B : Set ℕ) (n : ℕ) : Prop :=
  ∀ x : ZMod n, x ≠ 0 → ∃! (a b : ℕ), a ∈ B ∧ b ∈ B ∧ (a - b : ZMod n) = x

/-- The main conjecture: any finite Sidon set can be embedded in a perfect
    difference set modulo p^2 + p + 1 for some prime p. -/
@[category research open, AMS 5 11]
theorem erdos_707 : (∀ (A : Finset ℕ), IsSidonSet A →
    ∃ (B : Set ℕ) (p : ℕ), p.Prime ∧ A.toSet ⊆ B ∧ IsPerfectDifferenceSetModulo B (p^2 + p + 1)) ↔
    answer(sorry) := by
  sorry

/-- A variant asking for the smallest possible prime p. -/
@[category research open, AMS 5 11]
theorem erdos_707.smallest_prime : (∀ (A : Finset ℕ), IsSidonSet A →
    ∃ (B : Set ℕ) (p : ℕ), p.Prime ∧ A.toSet ⊆ B ∧ IsPerfectDifferenceSetModulo B (p^2 + p + 1) ∧
    ∀ (q : ℕ), q.Prime → q < p → ¬∃ (C : Set ℕ), A.toSet ⊆ C ∧ IsPerfectDifferenceSetModulo C (q^2 + q + 1)) ↔
    answer(sorry) := by
  sorry

/-- A constructive version asking for explicit bounds on the size of p in terms of |A|. -/
@[category research open, AMS 5 11]
theorem erdos_707.constructive : (∃ (f : ℕ → ℕ), ∀ (A : Finset ℕ), IsSidonSet A →
    ∃ (B : Set ℕ) (p : ℕ), p.Prime ∧ p ≤ f A.card ∧ A.toSet ⊆ B ∧
    IsPerfectDifferenceSetModulo B (p^2 + p + 1)) ↔
    answer(sorry) := by
  sorry

/-- A weaker version asking for any modulus, not necessarily of the form p^2 + p + 1. -/
@[category research open, AMS 5 11]
theorem erdos_707.weaker : (∀ (A : Finset ℕ), IsSidonSet A →
    ∃ (B : Set ℕ) (n : ℕ), A.toSet ⊆ B ∧ IsPerfectDifferenceSetModulo B n) ↔
    answer(sorry) := by
  sorry

/-! ## Perfect difference sets and their properties -/

/-- A perfect difference set modulo n must have size approximately √n. -/
@[category undergraduate, AMS 5 11]
theorem perfect_difference_set_size_bound (B : Set ℕ) (n : ℕ) (hB : IsPerfectDifferenceSetModulo B n) :
    B.ncard ≤ n.sqrt + 1 := by
  sorry

/-- The Singer construction gives perfect difference sets for n = p^2 + p + 1
    where p is a prime power. -/
@[category undergraduate, AMS 5 11]
theorem singer_construction (p : ℕ) (hp : p.Prime) :
    ∃ (B : Set ℕ), IsPerfectDifferenceSetModulo B (p^2 + p + 1) ∧ B.ncard = p + 1 := by
  sorry

/-- The projective plane construction gives perfect difference sets. -/
@[category undergraduate, AMS 5 11]
theorem projective_plane_construction (q : ℕ) (hq : IsPrimePower q) :
    ∃ (B : Set ℕ), IsPerfectDifferenceSetModulo B (q^2 + q + 1) := by
  sorry

/-! ## Examples and special cases -/

/-- The set {1, 2, 4} is a Sidon set. -/
@[category undergraduate, AMS 5 11]
theorem example_sidon_set : IsSidonSet {1, 2, 4} := by
  sorry

/-- The set {1, 2, 4} can be embedded in a perfect difference set modulo 7. -/
@[category undergraduate, AMS 5 11]
theorem example_embedding : ∃ (B : Set ℕ), {1, 2, 4} ⊆ B ∧ IsPerfectDifferenceSetModulo B 7 := by
  sorry

/-- For small Sidon sets, we can check the conjecture directly. -/
@[category undergraduate, AMS 5 11]
theorem small_sidon_sets : ∀ (A : Finset ℕ), A.card ≤ 3 → IsSidonSet A →
    ∃ (B : Set ℕ) (p : ℕ), p.Prime ∧ A.toSet ⊆ B ∧ IsPerfectDifferenceSetModulo B (p^2 + p + 1) := by
  sorry

/-! ## Connection to Erdős Problem 329 -/

/-- If Erdős Problem 707 is true, then the maximum density of Sidon sets is 1. -/
@[category research open, AMS 5 11]
theorem erdos_707_implies_329 :
    (∀ (A : Finset ℕ), IsSidonSet A →
        ∃ (B : Set ℕ) (p : ℕ), p.Prime ∧ A.toSet ⊆ B ∧ IsPerfectDifferenceSetModulo B (p^2 + p + 1)) →
    sSup {sidonUpperDensity A | (A : Set ℕ) (_ : A.IsSidonSet)} = 1 := by
  sorry

/-- The converse implication: if the maximum density is 1, then Problem 707 holds. -/
@[category research open, AMS 5 11]
theorem erdos_329_implies_707 :
    (sSup {sidonUpperDensity A | (A : Set ℕ) (_ : A.IsSidonSet)} = 1) →
    (∀ (A : Finset ℕ), IsSidonSet A →
        ∃ (B : Set ℕ) (p : ℕ), p.Prime ∧ A.toSet ⊆ B ∧ IsPerfectDifferenceSetModulo B (p^2 + p + 1)) := by
  sorry
