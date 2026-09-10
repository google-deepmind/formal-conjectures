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

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# A coefficient field inside the complex numbers

A field `K` with an algebra map to `ℂ` embeds `K`-linearly, and that embedding splits: an
injective linear map of vector spaces over a field has a left inverse. Choosing one gives a
`K`-linear retraction `ℂ → K`, which is what lets a complex cohomology class be pushed back to
`K`-coefficients.

Multiplication by a scalar, as an additive endomorphism, is recorded here alongside it. It is
kept free of the geometry so the constant-sheaf and cohomology developments can use it without
carrying the algebra hypothesis.
-/

@[expose] public noncomputable section

variable (K : Type) [Field K] [Algebra K ℂ]

/-- The inclusion of `K` into `ℂ`, regarded as a rational-linear map. -/
def fieldToComplexLinear : K →ₗ[K] ℂ :=
  Algebra.linearMap K ℂ

/-- A rational-linear retraction of the inclusion `K → ℂ`. Such a retraction exists because an
injective linear map of vector spaces over a field splits. -/
noncomputable def complexToFieldLinear : ℂ →ₗ[K] K :=
  Classical.choose <| (fieldToComplexLinear K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap K ℂ).injective)

/-- The chosen rational-linear retraction is a left inverse to `K → ℂ`. -/
lemma complexToFieldLinear_comp_fieldToComplexLinear :
    complexToFieldLinear K ∘ₗ fieldToComplexLinear K = LinearMap.id :=
  Classical.choose_spec <| (fieldToComplexLinear K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap K ℂ).injective)

@[simp] lemma complexToFieldLinear_algebraMap (q : K) :
    complexToFieldLinear K (algebraMap K ℂ q) = q := by
  have h := LinearMap.congr_fun (complexToFieldLinear_comp_fieldToComplexLinear K) q
  simpa [fieldToComplexLinear] using h

/-- Multiplication by a rational scalar as an additive endomorphism of `K`. -/
def fieldScalarAddHom (q : K) : K →+ K :=
  DistribSMul.toAddMonoidHom K q

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarAddHom_apply (q x : K) :
    fieldScalarAddHom K q x = q * x := rfl

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarAddHom_zero : fieldScalarAddHom K 0 = 0 := by
  ext
  simp

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarAddHom_one : fieldScalarAddHom K 1 = AddMonoidHom.id K := by
  ext
  simp

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarAddHom_add (a b : K) :
    fieldScalarAddHom K (a + b) = fieldScalarAddHom K a + fieldScalarAddHom K b := by
  ext
  simp [add_mul]

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarAddHom_mul (a b : K) :
    fieldScalarAddHom K (a * b) =
      (fieldScalarAddHom K a).comp (fieldScalarAddHom K b) := by
  ext
  simp [fieldScalarAddHom, mul_assoc]
