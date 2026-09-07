/-
Copyright 2025 The Formal Conjectures Authors.

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

# The Bass Quillen Conjecture

-/

namespace «1810.00617»

universe u

variable (R : Type u) [CommRing R] (ι : Type*) [Finite ι]

open TensorProduct IsLocalRing

/-- The `Bass Quillen Conjecture`, stating that any fg projective module over polynomial ring
over regular ring `R` comes from a projective module over `R`. -/
@[category research open, AMS 13]
theorem BassQuillenConjecture [IsRegularRing R] (P : Type*) [AddCommGroup P] [Module R P]
    [Module (MvPolynomial ι R) P] [IsScalarTower R (MvPolynomial ι R) P]
    [Module.Projective (MvPolynomial ι R) P] :
    ∃ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q),
      Nonempty (((MvPolynomial ι R) ⊗[R] Q) ≃ₗ[MvPolynomial ι R] P) := by
  sorry

section lowdimesnion

/-- The `Bass Quillen Conjecture` is true for dimension less than `2`. -/
@[category research solved, AMS 13]
theorem BassQuillenConjecture_of_dim_le_two [IsRegularRing R] (le2 : ringKrullDim R ≤ 2)
    (P : Type*) [AddCommGroup P] [Module R P]
    [Module (MvPolynomial ι R) P] [IsScalarTower R (MvPolynomial ι R) P]
    [Module.Projective (MvPolynomial ι R) P] :
    ∃ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q),
      Nonempty (((MvPolynomial ι R) ⊗[R] Q) ≃ₗ[MvPolynomial ι R] P) := by
  sorry

/-- The `Bass Quillen Conjecture` is true for local ring of dimension `3` with characteristic not
`2` or `3`. -/
@[category research solved, AMS 13]
theorem BassQuillenConjecture_of_dim_eq_three [IsRegularLocalRing R] (le2 : ringKrullDim R = 3)
    (ne2 : ringChar (ResidueField R) ≠ 2) (ne3 : ringChar (ResidueField R) ≠ 3)
    (P : Type*) [AddCommGroup P] [Module R P]
    [Module (MvPolynomial ι R) P] [IsScalarTower R (MvPolynomial ι R) P]
    [Module.Projective (MvPolynomial ι R) P] :
    ∃ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q),
      Nonempty (((MvPolynomial ι R) ⊗[R] Q) ≃ₗ[MvPolynomial ι R] P) := by
  sorry

end lowdimesnion

/-- The `Bass Quillen Conjecture` is true for local ring of char zero. -/
@[category research solved, AMS 13]
theorem BassQuillenConjecture_of_char_zero [IsRegularLocalRing R] [CharZero (ResidueField R)]
    (P : Type*) [AddCommGroup P] [Module R P]
    [Module (MvPolynomial ι R) P] [IsScalarTower R (MvPolynomial ι R) P]
    [Module.Projective (MvPolynomial ι R) P] :
    ∃ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q),
      Nonempty (((MvPolynomial ι R) ⊗[R] Q) ≃ₗ[MvPolynomial ι R] P) := by
  sorry

/-- The `Bass Quillen Conjecture` is true for local ring that is unramified. -/
@[category research solved, AMS 13]
theorem BassQuillenConjecture_of_unramified [IsRegularLocalRing R]
    (unram : (ringChar (ResidueField R) : R) ∉ (maximalIdeal R) ^ 2)
    (P : Type*) [AddCommGroup P] [Module R P]
    [Module (MvPolynomial ι R) P] [IsScalarTower R (MvPolynomial ι R) P]
    [Module.Projective (MvPolynomial ι R) P] :
    ∃ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q),
      Nonempty (((MvPolynomial ι R) ⊗[R] Q) ≃ₗ[MvPolynomial ι R] P) := by
  sorry

end «1810.00617»
