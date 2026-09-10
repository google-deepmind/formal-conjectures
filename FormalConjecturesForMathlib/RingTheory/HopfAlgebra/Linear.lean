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

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Multiplicative matrices and linear affine group schemes

An affine group scheme over a commutative ring `R` is `Spec A` for a commutative `R`-Hopf algebra
`A`. This file says what it means for such a group scheme to be *linear*, that is, a closed
subgroup scheme of some `GLₙ`.

## Main definitions

* `Matrix.IsMultiplicative R a`: the entries of a square matrix `a` over a bialgebra `A` satisfy
  `Δ aᵢⱼ = ∑ₖ aᵢₖ ⊗ aₖⱼ` and `ε aᵢⱼ = δᵢⱼ`. Such matrices are exactly the homomorphisms of group
  schemes `Spec A → GLₙ`: `a` is the image of the matrix of coordinates of `GLₙ` under the
  corresponding map of Hopf algebras.
* `HopfAlgebra.IsLinear R A`: the entries of some multiplicative matrix over `A` generate `A` as
  an `R`-algebra, that is, `Spec A` is a closed subgroup scheme of some `GLₙ`.

## Main results

* `Matrix.IsMultiplicative.isGroupLikeElem_det`: the determinant of a multiplicative matrix is
  group-like, hence a unit by `IsGroupLikeElem.isUnit`. A multiplicative matrix therefore does
  define a homomorphism into `GLₙ`, and not merely into the monoid scheme of `n × n` matrices.
* `HopfAlgebra.isLinear_self` and `LaurentPolynomial.isLinear`: the trivial group scheme and the
  multiplicative group are linear.

## Implementation notes

`HopfAlgebra.IsLinear` asks that the entries of `a` alone generate `A`. Bruhat and Tits state the
criterion for `Spec A → GLₙ` to be a closed immersion with `(det a)⁻¹` adjoined as well. The two
conditions agree: `(det a)⁻¹` is group-like, so appending it to `a` as an extra diagonal entry
gives a multiplicative matrix, one size larger, whose entries generate `A`.

## References

- [F. Bruhat and J. Tits, *Groupes réductifs sur un corps local
  II*](http://www.numdam.org/item/PMIHES_1984__60__5_0/), 1.4.5
-/

@[expose] public section

open Coalgebra TensorProduct

universe u v w

namespace Matrix

/-- A square matrix `a` over a bialgebra `A` is *multiplicative* when `Δ aᵢⱼ = ∑ₖ aᵢₖ ⊗ aₖⱼ` and
`ε aᵢⱼ = δᵢⱼ`.

Multiplicative matrices indexed by `ι` are exactly the homomorphisms of group schemes
`Spec A → GL(ι)`: such a matrix is the image of the matrix of coordinates of `GL(ι)` under the
induced map of Hopf algebras. No invertibility hypothesis is needed, by
`Matrix.IsMultiplicative.isGroupLikeElem_det`. -/
structure IsMultiplicative (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A]
    {ι : Type w} [Fintype ι] [DecidableEq ι] (a : Matrix ι ι A) : Prop where
  /-- The comultiplication of an entry is given by matrix multiplication. -/
  comul_apply : ∀ i j, comul (R := R) (a i j) = ∑ k, a i k ⊗ₜ[R] a k j
  /-- The counit of the matrix is the identity matrix. -/
  counit_apply : ∀ i j, counit (R := R) (a i j) = (1 : Matrix ι ι R) i j

/-- A `1 × 1` matrix is multiplicative exactly when its entry is group-like, that is, exactly when
it is a character `Spec A → GL₁ = 𝔾ₘ`. -/
theorem isMultiplicative_fin_one_iff (R : Type u) [CommRing R] {A : Type v} [CommRing A]
    [Bialgebra R A] (x : A) : IsMultiplicative R !![x] ↔ IsGroupLikeElem R x := by
  constructor
  · intro h
    exact ⟨by simpa using h.counit_apply 0 0, by simpa using h.comul_apply 0 0⟩
  · intro h
    refine ⟨fun i j ↦ ?_, fun i j ↦ ?_⟩
    · fin_cases i; fin_cases j; simpa using h.comul_eq_tmul_self
    · fin_cases i; fin_cases j; simpa using h.counit_eq_one

/-- The determinant of a multiplicative matrix is a group-like element. Over a Hopf algebra it is
therefore a unit, by `IsGroupLikeElem.isUnit`, so a multiplicative matrix defines a homomorphism
of group schemes into `GL(ι)` and not merely into the monoid scheme of matrices. -/
theorem IsMultiplicative.isGroupLikeElem_det {R : Type u} [CommRing R] {A : Type v} [CommRing A]
    [Bialgebra R A] {ι : Type w} [Fintype ι] [DecidableEq ι] {a : Matrix ι ι A}
    (h : IsMultiplicative R a) : IsGroupLikeElem R a.det where
  counit_eq_one := by
    have h1 : (Bialgebra.counitAlgHom R A).mapMatrix a = 1 := by
      ext i j
      simpa using h.counit_apply i j
    have h0 := AlgHom.map_det (Bialgebra.counitAlgHom R A) a
    rw [h1, Matrix.det_one] at h0
    simpa using h0
  comul_eq_tmul_self := by
    have h2 : (Bialgebra.comulAlgHom R A).mapMatrix a =
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := A)).mapMatrix a *
          (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A)).mapMatrix a := by
      ext i j
      rw [Matrix.mul_apply]
      simpa using h.comul_apply i j
    have h3 := AlgHom.map_det (Bialgebra.comulAlgHom R A) a
    rw [h2, Matrix.det_mul, ← AlgHom.map_det, ← AlgHom.map_det] at h3
    simpa using h3

end Matrix

namespace HopfAlgebra

/-- The affine group scheme `Spec A` over `R` is *linear* when it is a closed subgroup scheme of
some `GLₙ`, that is, when the entries of some multiplicative `n × n` matrix over `A` generate `A`
as an `R`-algebra. -/
def IsLinear (R : Type u) [CommRing R] (A : Type v) [CommRing A] [HopfAlgebra R A] : Prop :=
  ∃ (n : ℕ) (a : Matrix (Fin n) (Fin n) A), Matrix.IsMultiplicative R a ∧
    Algebra.adjoin R (Set.range fun ij : Fin n × Fin n ↦ a ij.1 ij.2) = ⊤

/-- The trivial group scheme `Spec R` is linear, via the empty matrix. -/
theorem isLinear_self (R : Type u) [CommRing R] : IsLinear R R := by
  refine ⟨0, (0 : Matrix (Fin 0) (Fin 0) R), ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩, ?_⟩
  exact Subsingleton.elim _ _

end HopfAlgebra

namespace LaurentPolynomial

/-- The multiplicative group `𝔾ₘ = Spec R[T, T⁻¹]` is linear: it is the diagonal torus
`diag(T, T⁻¹)` of `GL₂`. The `1 × 1` matrix `(T)` is multiplicative too, but `T` generates only
the polynomial subring `R[T]`, which is why a larger matrix is needed. -/
theorem isLinear (R : Type u) [CommRing R] : HopfAlgebra.IsLinear R (LaurentPolynomial R) := by
  refine ⟨2, !![T 1, 0; 0, T (-1)], ⟨fun i j ↦ ?_, fun i j ↦ ?_⟩, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two, LaurentPolynomial.comul_T]
  · fin_cases i <;> fin_cases j <;> simp [LaurentPolynomial.counit_T]
  · set S := Algebra.adjoin R (Set.range fun ij : Fin 2 × Fin 2 ↦
      (!![T 1, 0; 0, T (-1)] : Matrix (Fin 2) (Fin 2) (LaurentPolynomial R)) ij.1 ij.2)
    have h1 : (T 1 : LaurentPolynomial R) ∈ S := Algebra.subset_adjoin ⟨(0, 0), by simp⟩
    have h2 : (T (-1) : LaurentPolynomial R) ∈ S := Algebra.subset_adjoin ⟨(1, 1), by simp⟩
    have hT : ∀ n : ℤ, (T n : LaurentPolynomial R) ∈ S := by
      intro n
      rcases le_or_gt 0 n with h | h
      · lift n to ℕ using h
        have : (T (n : ℤ) : LaurentPolynomial R) = T 1 ^ n := by simp
        rw [this]
        exact pow_mem h1 n
      · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨n.natAbs, by omega⟩
        have : (T (-(m : ℤ)) : LaurentPolynomial R) = T (-1) ^ m := by rw [T_pow]; ring_nf
        rw [this]
        exact pow_mem h2 m
    refine Algebra.eq_top_iff.2 fun p ↦ ?_
    induction p using LaurentPolynomial.induction_on' with
    | add p q hp hq => exact add_mem hp hq
    | C_mul_T n a =>
      exact mul_mem (by rw [C_eq_algebraMap]; exact Subalgebra.algebraMap_mem S a) (hT n)

end LaurentPolynomial
