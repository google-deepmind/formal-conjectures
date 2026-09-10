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

public import FormalConjecturesForMathlib.Algebra.PolynomialCatenary
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.QuasiFinite.Basic

import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.NoetherNormalization

/-!
# Krull dimension and transcendence degree over a field

For a finitely generated domain over a field, the Krull dimension and the transcendence degree of
the fraction field agree. Both are therefore available to compute the dimension of a prime
quotient, whose transcendence degree is that of the residue field at the prime.

A quasi-finite algebra does not change the residue field's transcendence degree, so for finitely
generated algebras it does not change the dimension of a prime quotient either. This is the
commutative-algebra half of the catenary dimension formula for smooth complex schemes.
-/

@[expose] public noncomputable section

open Ideal MvPolynomial

namespace Algebra

variable {k A : Type} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- A finite-type domain over a field has a finite Krull dimension, and that dimension is its
transcendence degree.  The natural number is obtained from Noether normalization. -/
lemma FiniteType.exists_ringKrullDim_eq_and_trdeg_eq :
    ∃ n : ℕ, ringKrullDim A = n ∧ Algebra.trdeg k A = n := by
  obtain ⟨n, g, hg, hfinite⟩ := exists_finite_inj_algHom_of_fg k A
  let : Algebra (MvPolynomial (Fin n) k) A := g.toAlgebra
  let : FaithfulSMul (MvPolynomial (Fin n) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  let : IsScalarTower k (MvPolynomial (Fin n) k) A :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r => (g.commutes r).symm)
  let : Algebra.IsIntegral (MvPolynomial (Fin n) k) A :=
    ⟨hfinite.to_isIntegral⟩
  refine ⟨n, ?_, ?_⟩
  · rw [PolynomialCatenary.ringKrullDim_eq_of_isIntegral_of_injective hg,
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, Nat.card_fin]
    simp
  · have h := trdeg_add_eq k (MvPolynomial (Fin n) k) (A := A)
    have hzero : Algebra.trdeg (MvPolynomial (Fin n) k) A = 0 := trdeg_eq_zero
    rw [hzero, add_zero, MvPolynomial.trdeg_of_isDomain,
      Cardinal.mk_fin, Cardinal.lift_id] at h
    exact h.symm

variable {R : Type} [CommRing R] [Algebra k R]

/-- Passing from a prime quotient to its fraction field preserves transcendence degree. -/
lemma trdeg_quotient_eq_residueField (P : Ideal R) [P.IsPrime] :
    Algebra.trdeg k (R ⧸ P) = Algebra.trdeg k P.ResidueField := by
  have h := trdeg_add_eq k (R ⧸ P) (A := P.ResidueField)
  have hzero : Algebra.trdeg (R ⧸ P) P.ResidueField = 0 := trdeg_eq_zero
  rw [hzero, add_zero] at h
  exact h

variable {S : Type} [CommRing S] [Algebra k S] [Algebra R S]
  [IsScalarTower k R S] [Algebra.QuasiFinite R S]

/-- A quasi-finite map induces an algebraic extension between the residue fields of a prime and
its contraction, so their transcendence degrees over the ground field agree. -/
lemma QuasiFinite.trdeg_residueField_eq (P : Ideal S) [P.IsPrime] :
    Algebra.trdeg k P.ResidueField =
      Algebra.trdeg k (P.under R).ResidueField := by
  let q : Ideal R := P.under R
  let : P.LiesOver q := ⟨rfl⟩
  let : Algebra (Localization.AtPrime q) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver q P
  let : Module.Finite q.ResidueField P.ResidueField := inferInstance
  have h := trdeg_add_eq k q.ResidueField (A := P.ResidueField)
  have hzero : Algebra.trdeg q.ResidueField P.ResidueField = 0 := trdeg_eq_zero
  rw [hzero, add_zero] at h
  exact h.symm

variable [Algebra.FiniteType k R] [Algebra.FiniteType k S]

include k in
/-- A quasi-finite map between finite-type algebras over a field preserves the Krull dimension of
the quotient at a prime.  This does not assert that the induced quotient map is flat. -/
lemma QuasiFinite.ringKrullDim_quotient_eq (P : Ideal S) [P.IsPrime] :
    ringKrullDim (S ⧸ P) = ringKrullDim (R ⧸ P.under R) := by
  let q : Ideal R := P.under R
  let : q.IsPrime := Ideal.IsPrime.comap (algebraMap R S)
  let : Algebra.FiniteType k (R ⧸ q) := Algebra.FiniteType.quotient k q
  let : Algebra.FiniteType k (S ⧸ P) := Algebra.FiniteType.quotient k P
  obtain ⟨n, hnDim, hnTrdeg⟩ :=
    FiniteType.exists_ringKrullDim_eq_and_trdeg_eq (k := k) (A := R ⧸ q)
  obtain ⟨m, hmDim, hmTrdeg⟩ :=
    FiniteType.exists_ringKrullDim_eq_and_trdeg_eq (k := k) (A := S ⧸ P)
  have htr : Algebra.trdeg k (S ⧸ P) = Algebra.trdeg k (R ⧸ q) :=
    (trdeg_quotient_eq_residueField (k := k) P).trans
      ((QuasiFinite.trdeg_residueField_eq (k := k) (R := R) P).trans
        (trdeg_quotient_eq_residueField (k := k) q).symm)
  have hmnCard : (m : Cardinal) = (n : Cardinal) :=
    hmTrdeg.symm.trans (htr.trans hnTrdeg)
  have hmn : m = n := by exact_mod_cast hmnCard
  rw [hmDim, hnDim, hmn]

end Algebra
