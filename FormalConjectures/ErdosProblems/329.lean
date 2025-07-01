/
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
# Erdős Problem 329: Maximum Density of Sidon Sets

*Reference:* [erdosproblems.com/329](https://www.erdosproblems.com/329)

Suppose A ⊆ ℕ is a Sidon set. How large can
lim sup_{N→∞} |A ∩ {1,…,N}| / N^(1/2)
be?

Erdős proved that 1/2 is possible and Krückeberg [Kr61] proved 1/2 is possible.
Erdős and Turán [ErTu41] have proved this lim sup is always ≤ 1.

The fact that 1 is possible would follow if any finite Sidon set is a subset of a perfect difference set.
-/

open Function Set Filter

/-- A set A is a Sidon set if all pairwise sums are distinct. -/
def Set.IsSidonSet (A : Set ℕ) : Prop :=
  ∀ a b c d ∈ A, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The density of a Sidon set A up to N. -/
def sidonDensity (A : Set ℕ) (N : ℕ) : ℝ :=
  (A ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt

/-- The upper density of a Sidon set A. -/
noncomputable def sidonUpperDensity (A : Set ℕ) : ℝ :=
  limsup (fun N => sidonDensity A N) atTop

/-- The main question: what is the maximum possible upper density of a Sidon set? -/
@[category research open, AMS 5 11]
theorem erdos_329 : sSup {sidonUpperDensity A | (A : Set ℕ) (_ : A.IsSidonSet)} = answer(sorry) := by
  sorry

/-- Erdős proved that 1/2 is achievable as an upper density. -/
@[category research solved, AMS 5 11]
theorem erdos_329.lower_bound : ∃ (A : Set ℕ), A.IsSidonSet ∧ sidonUpperDensity A ≥ 1/2 := by
  sorry

/-- Krückeberg [Kr61] proved that 1/2 is achievable. -/
@[category research solved, AMS 5 11]
theorem kruckeberg_1961 : ∃ (A : Set ℕ), A.IsSidonSet ∧ sidonUpperDensity A = 1/2 := by
  sorry

/-- Erdős and Turán [ErTu41] proved the upper bound of 1. -/
@[category research solved, AMS 5 11]
theorem erdos_turan_1941 : ∀ (A : Set ℕ), A.IsSidonSet → sidonUpperDensity A ≤ 1 := by
  sorry

/-- A perfect difference set modulo n is a set D such that every non-zero element
    of Z/nZ can be written as a difference of two elements of D in exactly one way. -/
def IsPerfectDifferenceSet (D : Set ℕ) (n : ℕ) : Prop :=
  let D_mod := {d % n | d ∈ D}
  ∀ x : ZMod n, x ≠ 0 → ∃! (a b : ℕ), a ∈ D ∧ b ∈ D ∧ (a - b : ZMod n) = x

/-- If any finite Sidon set can be embedded in a perfect difference set,
    then the maximum density would be 1. -/
@[category research open, AMS 5 11]
theorem erdos_329.perfect_difference_set_implication :
    (∀ (A : Finset ℕ), IsSidonSet A.toSet → ∃ (D : Set ℕ) (n : ℕ),
      A.toSet ⊆ D ∧ IsPerfectDifferenceSet D n) →
    sSup {sidonUpperDensity A | (A : Set ℕ) (_ : A.IsSidonSet)} = 1 := by
  sorry

/-- The converse: if the maximum density is 1, then any finite Sidon set
    can be embedded in a perfect difference set. -/
@[category research open, AMS 5 11]
theorem erdos_329.converse_implication :
    (sSup {sidonUpperDensity A | (A : Set ℕ) (_ : A.IsSidonSet)} = 1) →
    (∀ (A : Finset ℕ), IsSidonSet A.toSet → ∃ (D : Set ℕ) (n : ℕ),
      A.toSet ⊆ D ∧ IsPerfectDifferenceSet D n) := by
  sorry

/-! ## Related results and examples -/

/-- The set of squares {1, 4, 9, 16, ...} is a Sidon set. -/
@[category undergraduate, AMS 5 11]
theorem squares_are_sidon : IsSidonSet {n^2 | n : ℕ} := by
  sorry

/-- The set of squares has upper density 0. -/
@[category undergraduate, AMS 5 11]
theorem squares_sidon_density : sidonUpperDensity {n^2 | n : ℕ} = 0 := by
  sorry

/-- The greedy construction gives a Sidon set with positive density. -/
@[category undergraduate, AMS 5 11]
theorem greedy_sidon_construction : ∃ (A : Set ℕ), A.IsSidonSet ∧ 0 < sidonUpperDensity A := by
  sorry

/-- A Sidon set cannot have density greater than 1. -/
@[category undergraduate, AMS 5 11]
theorem sidon_density_upper_bound (A : Set ℕ) (hA : A.IsSidonSet) :
    sidonUpperDensity A ≤ 1 := by
  sorry
