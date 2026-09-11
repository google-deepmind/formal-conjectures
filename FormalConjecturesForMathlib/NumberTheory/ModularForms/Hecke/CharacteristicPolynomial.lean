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

public import FormalConjecturesForMathlib.NumberTheory.ModularForms.Hecke.LevelOne
public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

@[expose] public section

/-!
# The characteristic polynomial of a Hecke operator

`LevelOne.lean` builds the Hecke operator `T_n` as a `ℂ`-linear endomorphism
`CuspForm.heckeOperatorₗ k n` of `CuspForm 𝒮ℒ k`, the space of cusp forms of weight `k` and level
one. The space is finite-dimensional (`CuspForm.instFiniteDimensional`), so the operator has a
characteristic polynomial `CuspForm.heckeCharpoly k n : ℂ[X]`, which is monic of degree
`dim S_k`. Maeda's conjecture, that this polynomial comes from a rational polynomial which is
irreducible over `ℚ` with full symmetric Galois group, is stated in
`FormalConjectures/Arxiv/1207.3480/Maeda.lean`.

## Design

The operator is kept `ℂ`-linear, and rationality is expressed as
`∃ P : ℚ[X], P.map (algebraMap ℚ ℂ) = heckeCharpoly k n`. This avoids developing a rational
structure on the space of cusp forms, and avoids defining a rational polynomial by choosing a
witness of an existence theorem: a property of the rational polynomial is stated by quantifying
over the witness existentially, and `eq_of_map_eq_heckeCharpoly` shows that the witness is unique.
That the witness exists, i.e. that the characteristic polynomial has rational coefficients, is
classical (Serre, *A course in arithmetic*, Chapter VII, §5) but is not proved here.

## Main definitions

* `CuspForm.heckeCharpoly k n`: the characteristic polynomial of `T_n` on `S_k`.

## Main results

* `CuspForm.instFiniteDimensional`: `S_k` is finite-dimensional over `ℂ`.
* `CuspForm.heckeCharpoly_monic`, `CuspForm.natDegree_heckeCharpoly`: monicity and degree.
* `CuspForm.eq_of_map_eq_heckeCharpoly`: uniqueness of a rational polynomial giving the
  characteristic polynomial.
* `CuspForm.natDegree_of_map_eq_heckeCharpoly`: such a rational polynomial has degree `dim S_k`.
* `CuspForm.finrank_eq_one_of_weight_eq_twelve`: `S_12` is one-dimensional.

## References

* H. Hida and Y. Maeda, *Non-abelian base change for totally real fields*,
  Pacific J. Math. 181 (1997), Special Issue, 189–217, Conjecture 1.2.
* A. Ghitza and A. McAndrew, *Experimental evidence for Maeda's conjecture on modular forms*,
  Tbilisi Math. J. 5 (2012), 55–69, Conjecture 1.1 (<https://arxiv.org/abs/1207.3480>).
* J.-P. Serre, *A course in arithmetic*, Chapter VII, §5.
-/

open Module Polynomial

open scoped MatrixGroups

namespace CuspForm

/-- Level-one cusp forms of weight `k` form a finite-dimensional `ℂ`-vector space: they inject
into the modular forms of weight `k`, which are finite-dimensional. -/
instance instFiniteDimensional {k : ℤ} : FiniteDimensional ℂ (CuspForm 𝒮ℒ k) :=
  .of_injective (toModularFormₗ : CuspForm 𝒮ℒ k →ₗ[ℂ] ModularForm 𝒮ℒ k)
    toModularFormₗ_injective

variable (k : ℤ) (n : ℕ)

/-- **The characteristic polynomial of `T_n` on `S_k`**, as a polynomial over `ℂ`. -/
noncomputable def heckeCharpoly : ℂ[X] := (heckeOperatorₗ k n).charpoly

/-- Unfolding lemma for `heckeCharpoly`. -/
theorem heckeCharpoly_eq_charpoly : heckeCharpoly k n = (heckeOperatorₗ k n).charpoly := rfl

/-- The characteristic polynomial of `T_n` is monic. -/
theorem heckeCharpoly_monic : (heckeCharpoly k n).Monic :=
  LinearMap.charpoly_monic _

/-- The characteristic polynomial of `T_n` has degree `dim_ℂ S_k`. -/
theorem natDegree_heckeCharpoly : (heckeCharpoly k n).natDegree = finrank ℂ (CuspForm 𝒮ℒ k) :=
  LinearMap.charpoly_natDegree _

/-- **Uniqueness**: the rational polynomial giving the characteristic polynomial is unique, since
`ℚ → ℂ` is injective. -/
theorem eq_of_map_eq_heckeCharpoly {P Q : ℚ[X]}
    (hP : P.map (algebraMap ℚ ℂ) = heckeCharpoly k n)
    (hQ : Q.map (algebraMap ℚ ℂ) = heckeCharpoly k n) : P = Q :=
  Polynomial.map_injective _ (algebraMap ℚ ℂ).injective (hP.trans hQ.symm)

/-- **Degree compatibility**: the rational polynomial has degree `dim S_k`. -/
theorem natDegree_of_map_eq_heckeCharpoly {P : ℚ[X]}
    (hP : P.map (algebraMap ℚ ℂ) = heckeCharpoly k n) :
    P.natDegree = finrank ℂ (CuspForm 𝒮ℒ k) := by
  rw [← natDegree_heckeCharpoly k n, ← hP, natDegree_map]

/-! ### Weight `12` -/

/-- `S_12` is one-dimensional, spanned by `Δ`. -/
theorem finrank_eq_one_of_weight_eq_twelve : finrank ℂ (CuspForm 𝒮ℒ 12) = 1 :=
  finrank_eq_of_rank_eq (mod_cast rank_eq_one_of_weight_eq_twelve)

end CuspForm

end
