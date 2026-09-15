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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.RelativeHomotopyInvariance
public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.ComplexOrientation
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Invariance of the complex local class under complex-linear coordinate changes

An invertible complex matrix is joined to the identity through invertible complex matrices.
The proof uses Mathlib's generation of invertible matrices by diagonal matrices and
transvections.  Diagonal entries are joined to one by `exp (t * log z)`, while a transvection is
joined to one by scaling its off-diagonal entry by `t`.

The resulting isotopy gives a homotopy of punctured pairs. Hence every complex-linear
automorphism acts trivially on the explicitly normalized standard complex local homology class.
This supplies the linear local-degree step needed to compare holomorphic coordinate charts; the
remaining nonlinear step is to replace a chart transition germ by its derivative.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An isotopy from the identity matrix to `A`, all of whose members are invertible. -/
structure ComplexIsotopyToOne (A : Matrix n n ℂ) where
  /-- The continuously varying matrix. -/
  path : C(unitInterval, Matrix n n ℂ)
  /-- The path begins at the identity. -/
  map_zero : path 0 = 1
  /-- The path ends at the specified matrix. -/
  map_one : path 1 = A
  /-- Every matrix along the path is invertible. -/
  det_ne_zero : ∀ t, (path t).det ≠ 0

namespace ComplexIsotopyToOne

/-- Pointwise multiplication concatenates isotopies algebraically.  This is the construction
used for products in the diagonal--transvection induction. -/
def mul {A B : Matrix n n ℂ}
    (hA : ComplexIsotopyToOne A) (hB : ComplexIsotopyToOne B) :
    ComplexIsotopyToOne (A * B) where
  path :=
    ⟨fun t ↦ hA.path t * hB.path t, by
      refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
      simp only [Matrix.mul_apply]
      fun_prop⟩
  map_zero := by
    change hA.path 0 * hB.path 0 = 1
    rw [hA.map_zero, hB.map_zero, Matrix.one_mul]
  map_one := by
    change hA.path 1 * hB.path 1 = A * B
    rw [hA.map_one, hB.map_one]
  det_ne_zero t := by
    change (hA.path t * hB.path t).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hA.det_ne_zero t) (hB.det_ne_zero t)

/-- An invertible diagonal complex matrix is isotopic to the identity. -/
def diagonal (D : n → ℂ) (hD : (Matrix.diagonal D).det ≠ 0) :
    ComplexIsotopyToOne (Matrix.diagonal D) := by
  have hDi : ∀ i, D i ≠ 0 := fun i hi ↦ hD <| by
    rw [Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  refine
    { path :=
        ⟨fun t ↦ Matrix.diagonal fun i ↦
            Complex.exp (((t : ℝ) : ℂ) * Complex.log (D i)), ?_⟩
      map_zero := ?_
      map_one := ?_
      det_ne_zero := ?_ }
  · refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    change Continuous (fun a : unitInterval ↦ if i = j then
      Complex.exp (((a : ℝ) : ℂ) * Complex.log (D i)) else 0)
    by_cases hij : i = j
    · simp only [hij, ↓reduceIte]
      fun_prop
    · simp only [hij, ↓reduceIte]
      exact continuous_const
  · ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij]
  · ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal, Complex.exp_log (hDi i)]
    · simp [Matrix.diagonal, hij]
  · intro t
    change (Matrix.diagonal (fun i ↦
      Complex.exp (((t : ℝ) : ℂ) * Complex.log (D i)))).det ≠ 0
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ Complex.exp_ne_zero _

/-- A complex transvection is isotopic to the identity by scaling its off-diagonal entry. -/
def transvection (t : Matrix.TransvectionStruct n ℂ) :
    ComplexIsotopyToOne t.toMatrix := by
  let P : C(unitInterval, Matrix n n ℂ) :=
    ⟨fun s ↦ Matrix.transvection t.i t.j (((s : ℝ) : ℂ) * t.c), by
      refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
      change Continuous (fun a : unitInterval ↦
        (1 : Matrix n n ℂ) i j +
          if t.i = i ∧ t.j = j then ((a : ℝ) : ℂ) * t.c else 0)
      by_cases h : t.i = i ∧ t.j = j
      · simp [h]
        fun_prop
      · simp [h]
        exact continuous_const⟩
  refine
    { path := P
      map_zero := ?_
      map_one := ?_
      det_ne_zero := ?_ }
  · simp [P]
  · simp [P, Matrix.TransvectionStruct.toMatrix]
  · intro s
    simpa only [P, ContinuousMap.coe_mk] using
      (show (Matrix.transvection t.i t.j (((s : ℝ) : ℂ) * t.c)).det ≠ 0 by
        rw [Matrix.det_transvection_of_ne _ _ t.hij]
        exact one_ne_zero)

end ComplexIsotopyToOne

/-- Every invertible complex matrix is isotopic to the identity through invertible matrices.

This is a concrete form of path connectedness of `GLₙ(ℂ)`, proved without taking that
path-connectedness as an imported black box. -/
theorem nonempty_complexIsotopyToOne (A : Matrix n n ℂ) (hA : A.det ≠ 0) :
    Nonempty (ComplexIsotopyToOne A) := by
  apply Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun B ↦ Nonempty (ComplexIsotopyToOne B)) A hA
  · intro D hD
    exact ⟨ComplexIsotopyToOne.diagonal D hD⟩
  · intro t
    exact ⟨ComplexIsotopyToOne.transvection t⟩
  · intro B C _hB _hC hB hC
    exact ⟨hB.some.mul hC.some⟩

end Matrix

namespace AlgebraicTopology.Singular

variable (d : ℕ)

/-- Joint continuity of matrix-vector multiplication along a continuous matrix path. -/
lemma continuous_complexMatrixPath_mulVec
    (H : C(unitInterval, Matrix (Fin d) (Fin d) ℂ)) :
    Continuous (fun tx : unitInterval × (Fin d → ℂ) ↦
      (H tx.1).mulVec tx.2) := by
  refine continuous_pi fun i ↦ ?_
  simp only [Matrix.mulVec, dotProduct]
  refine continuous_finsetSum _ fun j _ ↦ ?_
  exact
    ((continuous_apply j).comp
      ((continuous_apply i).comp (H.continuous.comp continuous_fst))).mul
        ((continuous_apply j).comp continuous_snd)

/-- Joint continuity on the punctured vector subspace. -/
lemma continuous_complexMatrixPath_mulVec_punctured
    (H : C(unitInterval, Matrix (Fin d) (Fin d) ℂ)) :
    Continuous (fun tx : unitInterval × ({0}ᶜ : Set (Fin d → ℂ)) ↦
      (H tx.1).mulVec tx.2.1) :=
  (continuous_complexMatrixPath_mulVec d H).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- The continuous self-map of complex affine space defined by a matrix. -/
def complexMatrixMap (A : Matrix (Fin d) (Fin d) ℂ) :
    TopCat.of (Fin d → ℂ) ⟶ TopCat.of (Fin d → ℂ) :=
  TopCat.ofHom ⟨A.mulVec, A.mulVecLin.continuous_of_finiteDimensional⟩

/-- The restriction of an invertible complex matrix to the complement of the origin. -/
lemma complexMatrix_mulVec_ne_zero
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.det ≠ 0)
    (z : ({0}ᶜ : Set (Fin d → ℂ))) : A.mulVec z.1 ≠ 0 := fun hz ↦
  z.2 (A.mulVec_injective_of_det_ne_zero hA (by simpa using hz))

/-- The restriction of an invertible complex matrix to the complement of the origin. -/
def complexMatrixPuncturedMap (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.det ≠ 0) :
    TopCat.of ({0}ᶜ : Set (Fin d → ℂ)) ⟶ TopCat.of ({0}ᶜ : Set (Fin d → ℂ)) :=
  TopCat.ofHom
    ⟨fun z ↦ ⟨A.mulVec z.1, complexMatrix_mulVec_ne_zero d A hA z⟩,
      Continuous.subtype_mk
        (A.mulVecLin.continuous_of_finiteDimensional.comp continuous_subtype_val)
        (complexMatrix_mulVec_ne_zero d A hA)⟩

@[simp]
lemma complexMatrixMap_apply (A : Matrix (Fin d) (Fin d) ℂ) (z : Fin d → ℂ) :
    complexMatrixMap d A z = A.mulVec z := rfl

@[simp]
lemma complexMatrixPuncturedMap_apply
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.det ≠ 0)
    (z : ({0}ᶜ : Set (Fin d → ℂ))) :
    (complexMatrixPuncturedMap d A hA z).1 = A.mulVec z.1 := rfl

/-- An invertible complex matrix acts on complex affine space and its punctured subspace. -/
def complexMatrixPuncturedPairMap (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.det ≠ 0) :
    standardComplexPuncturedPair d ⟶ standardComplexPuncturedPair d :=
  TopPair.ofHom (X := standardComplexPuncturedPair d)
    (Y := standardComplexPuncturedPair d)
    (complexMatrixMap d A)
    (complexMatrixPuncturedMap d A hA)
    (by
      apply TopCat.hom_ext
      ext z
      rfl)

/-- An isotopy of invertible matrices induces a homotopy of their maps of punctured pairs. -/
def complexMatrixPuncturedPairHomotopy
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.det ≠ 0)
    (H : Matrix.ComplexIsotopyToOne A) :
    TopPair.Homotopy (𝟙 (standardComplexPuncturedPair d))
      (complexMatrixPuncturedPairMap d A hA) where
  fst :=
    { toFun := fun tx ↦ (H.path tx.1).mulVec tx.2
      continuous_toFun := continuous_complexMatrixPath_mulVec d H.path
      map_zero_left := fun x ↦ by
        simp only [H.map_zero]
        exact Matrix.one_mulVec x
      map_one_left := fun x ↦ by
        simp only [H.map_one]
        rfl }
  snd :=
    { toFun := fun tx ↦
        ⟨(H.path tx.1).mulVec tx.2.1, by
          intro hz
          apply tx.2.2
          apply (H.path tx.1).mulVec_injective_of_det_ne_zero (H.det_ne_zero tx.1)
          simpa using hz⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_complexMatrixPath_mulVec_punctured d H.path
      map_zero_left := fun x ↦ by
        apply Subtype.ext
        simp only [H.map_zero]
        exact Matrix.one_mulVec x.1
      map_one_left := fun x ↦ by
        apply Subtype.ext
        simp only [H.map_one]
        rfl }
  w := rfl

/-- Every invertible complex matrix acts trivially on the standard complex local homology class.
-/
theorem relativeHomologyMap_complexMatrix_standardComplexLocalClass
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.det ≠ 0) :
    relativeHomologyMap ℚ (2 * d) (complexMatrixPuncturedPairMap d A hA)
        (standardComplexLocalClass d) =
      standardComplexLocalClass d := by
  let H := (Matrix.nonempty_complexIsotopyToOne A hA).some
  have h := (complexMatrixPuncturedPairHomotopy d hA H).relativeHomologyMap_apply_eq
    (R := ℚ) (2 * d) (standardComplexLocalClass d)
  simpa using h.symm

end AlgebraicTopology.Singular
