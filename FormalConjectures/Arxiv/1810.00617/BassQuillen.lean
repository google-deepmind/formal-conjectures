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

# The Bass Quillen Conjecture

*Reference:*

- [Bas73]
  **Some problems in 'classical' algebraic K-theory**
  by *Hyman Bass*, Algebraic K-Theory II, Lecture Notes in Mathematics,
  Vol. 342, Springer-Verlag, Berlin-Heidelberg-New York, (1973), Section 4.1, Problem IX.

- [Murty66](https://doi.org/10.1112/jlms/s1-41.1.453)
  **Projective A[X]-modules**
  by *M. P. Murty*, Journal of the London Mathematical Society, Volume 41, (1966), 453-456.

- [Rao88](https://doi.org/10.1007/BF01410201)
  **The Bass-Quillen conjecture in dimension three but characteristic ≠ 2,3 via a question of A. Suslin**
  by *R. Rao*, Inventiones Mathematicae, Volume 93, (1988), 609-618.

- [Lin81](https://doi.org/10.1007/BF01389017)
  **On the Bass-Quillen conjecture concerning projective modules over polynomial rings**
  by *Hartmut Lindel*, Inventiones Mathematicae, Volume 64, (1981), 319-324.

- [Swa82](https://doi.org/10.2307/1997613)
  **Projective modules over Laurent polynomial rings**
  by *R. G. Swan*, Transactions of the American Mathematical Society, Volume 273, (1982), 409-419.

- [Pop86](https://doi.org/10.1017/S0027763000022698)
  **General Néron desingularization and approximation**
  by *Dorin Popescu*, Nagoya Mathematical Journal, Volume 104, (1986), 85-115.

- [Pop89](https://doi.org/10.1017/S0027763000001288)
  **Polynomial rings and their projective modules**
  by *Dorin Popescu*, Nagoya Mathematical Journal, Volume 113, (1989), 121-128.

-/

namespace «1810.00617»

universe u

variable (R : Type u) [CommRing R] (ι : Type*) [Finite ι]

open TensorProduct IsLocalRing

/-- The `Bass Quillen Conjecture`, stating that any fg projective module over polynomial ring
over regular ring `R` comes from a projective module over `R`. [Bas73] -/
@[category research open, AMS 13]
theorem BassQuillenConjecture [IsRegularRing R] (P : Type u) [AddCommGroup P] [Module R P]
    [Module (MvPolynomial ι R) P] [IsScalarTower R (MvPolynomial ι R) P]
    [Module.Finite (MvPolynomial ι R) P] [Module.Projective (MvPolynomial ι R) P] :
    ∃ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q),
      Nonempty (((MvPolynomial ι R) ⊗[R] Q) ≃ₗ[MvPolynomial ι R] P) := by
  sorry

section lowdimesnion

/-- The `Bass Quillen Conjecture` is true for dimension less than `2`. [Murty66] -/
@[category research solved, AMS 13]
theorem BassQuillenConjecture_of_dim_le_two [IsRegularRing R] (le2 : ringKrullDim R ≤ 2)
    (P : Type u) [AddCommGroup P] [Module R P]
    [Module (MvPolynomial ι R) P] [IsScalarTower R (MvPolynomial ι R) P]
    [Module.Finite (MvPolynomial ι R) P] [Module.Projective (MvPolynomial ι R) P] :
    ∃ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q),
      Nonempty (((MvPolynomial ι R) ⊗[R] Q) ≃ₗ[MvPolynomial ι R] P) := by
  sorry

/-- The `Bass Quillen Conjecture` is true for local ring of dimension `3` with characteristic not
`2` or `3`. [Rao88] -/
@[category research solved, AMS 13]
theorem BassQuillenConjecture_of_dim_eq_three [IsRegularLocalRing R] (le2 : ringKrullDim R = 3)
    (ne2 : ringChar (ResidueField R) ≠ 2) (ne3 : ringChar (ResidueField R) ≠ 3)
    (P : Type u) [AddCommGroup P] [Module R P]
    [Module (MvPolynomial ι R) P] [IsScalarTower R (MvPolynomial ι R) P]
    [Module.Finite (MvPolynomial ι R) P] [Module.Projective (MvPolynomial ι R) P] :
    ∃ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q),
      Nonempty (((MvPolynomial ι R) ⊗[R] Q) ≃ₗ[MvPolynomial ι R] P) := by
  sorry

end lowdimesnion

/-
The following two results concerns *Corollary 5* of arxiv.org/abs/1810.00617, as a corollary from
combination of [Lin81], [Swa82], [Pop86], [Pop89].
-/

/-- The `Bass Quillen Conjecture` is true for local ring of char zero. -/
@[category research solved, AMS 13]
theorem BassQuillenConjecture_of_char_zero [IsRegularLocalRing R] [CharZero (ResidueField R)]
    (P : Type u) [AddCommGroup P] [Module R P]
    [Module (MvPolynomial ι R) P] [IsScalarTower R (MvPolynomial ι R) P]
    [Module.Finite (MvPolynomial ι R) P] [Module.Projective (MvPolynomial ι R) P] :
    ∃ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q),
      Nonempty (((MvPolynomial ι R) ⊗[R] Q) ≃ₗ[MvPolynomial ι R] P) := by
  sorry

/-- The `Bass Quillen Conjecture` is true for local ring that is unramified. -/
@[category research solved, AMS 13]
theorem BassQuillenConjecture_of_unramified [IsRegularLocalRing R]
    (unram : (ringChar (ResidueField R) : R) ∉ (maximalIdeal R) ^ 2)
    (P : Type u) [AddCommGroup P] [Module R P]
    [Module (MvPolynomial ι R) P] [IsScalarTower R (MvPolynomial ι R) P]
    [Module.Finite (MvPolynomial ι R) P] [Module.Projective (MvPolynomial ι R) P] :
    ∃ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q),
      Nonempty (((MvPolynomial ι R) ⊗[R] Q) ≃ₗ[MvPolynomial ι R] P) := by
  sorry

end «1810.00617»
