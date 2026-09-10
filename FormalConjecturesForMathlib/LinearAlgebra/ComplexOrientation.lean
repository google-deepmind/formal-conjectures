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

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Complex.Orientation
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Orientations of complex vector spaces

Every complex-linear automorphism preserves either real orientation of its underlying real vector
space.  This file proves that fact from the determinant norm formula and defines the standard
orientation of `Fin n → ℂ`, with real and imaginary basis vectors interleaved.

The generic preservation theorem is phrased using mathlib's `Orientation`.  In particular, it is
the linear-algebra input needed to construct the constant-sign `Manifold.OrientationLift` proposed
in [mathlib4 PR #35376](https://github.com/leanprover-community/mathlib4/pull/35376): apply
`Manifold.OrientationLift.compatible_of_det` to the positivity result after identifying a
holomorphic tangent coordinate change with the scalar restriction of a complex-linear
equivalence.
-/

@[expose] public noncomputable section

/-- A complex-linear automorphism has positive real determinant after restriction of scalars.

This is stated for an arbitrary finite free complex module.  The real freeness needed to form the
determinant is supplied by the scalar-tower instance behind `LinearMap.det_restrictScalars`.
-/
theorem LinearEquiv.det_restrictScalars_complex_pos
    {E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E]
    [IsScalarTower ℝ ℂ E] [Module.Free ℂ E]
    (f : E ≃ₗ[ℂ] E) :
    0 < LinearMap.det ((f.restrictScalars ℝ).toLinearMap) := by
  change 0 < LinearMap.det (f.toLinearMap.restrictScalars ℝ)
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  exact Complex.normSq_pos.mpr f.isUnit_det'.ne_zero

/-- A complex-linear automorphism preserves every real orientation after restriction of scalars. -/
theorem Orientation.map_restrictScalars_complexLinearEquiv
    {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E]
    [IsScalarTower ℝ ℂ E] [Module.Free ℂ E]
    [FiniteDimensional ℝ E] [Fintype ι]
    (f : E ≃ₗ[ℂ] E) (ω : Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E) :
    Orientation.map ι (f.restrictScalars ℝ) ω = ω := by
  rw [Orientation.map_eq_iff_det_pos ω (f.restrictScalars ℝ) hι]
  exact f.det_restrictScalars_complex_pos

namespace Complex

/-- The real dimension of `Fin n → ℂ` is `2 * n`, in the form expected by
`Manifold.OrientationLift`. -/
instance piOrientationFinrankFact (n : ℕ) :
    Fact (Fintype.card (Fin (n * 2)) = Module.finrank ℝ (Fin n → ℂ)) :=
  ⟨by simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]⟩

/-- The standard real basis of `Fin n → ℂ`, ordered
`(re z 0, im z 0, re z 1, im z 1, ...)`.

It is obtained by composing the standard complex basis of the function space with `basisOneI`,
then reindexing the product basis by `finProdFinEquiv`.
-/
def piBasisOneI (n : ℕ) : Module.Basis (Fin (n * 2)) ℝ (Fin n → ℂ) :=
  (basisOneI.smulTower' (Pi.basisFun ℂ (Fin n))).reindex finProdFinEquiv

/-- The canonical complex orientation of `Fin n → ℂ`, regarded as a real vector space. -/
def piOrientation (n : ℕ) : Orientation ℝ (Fin n → ℂ) (Fin (n * 2)) :=
  (piBasisOneI n).orientation

/-- Complex-linear automorphisms of `Fin n → ℂ` preserve its canonical complex orientation. -/
theorem map_piOrientation (n : ℕ) (f : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) :
    Orientation.map (Fin (n * 2)) (f.restrictScalars ℝ) (piOrientation n) =
      piOrientation n :=
  (Orientation.map_eq_iff_det_pos _ _
    (by rw [Module.finrank_eq_card_basis (piBasisOneI n)])).2
    f.det_restrictScalars_complex_pos

end Complex
