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

A field `K` with an algebra map to `ℂ` embeds `K`-linearly via `Algebra.linearMap`, and that
embedding splits: an
injective linear map of vector spaces over a field has a left inverse. Choosing one gives a
`K`-linear retraction `ℂ → K`, which is what lets a complex cohomology class be pushed back to
`K`-coefficients.

Multiplication by a scalar, as an additive endomorphism, is recorded here alongside it. It is
kept free of the geometry so the constant-sheaf and cohomology developments can use it without
carrying the algebra hypothesis.
-/

@[expose] public noncomputable section

variable (K : Type) [Field K] [Algebra K ℂ]

/-- A rational-linear retraction of the inclusion `K → ℂ`. Such a retraction exists because an
injective linear map of vector spaces over a field splits. -/
noncomputable def complexToFieldLinear : ℂ →ₗ[K] K :=
  Classical.choose <| (Algebra.linearMap K ℂ).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap K ℂ).injective)

/-- Multiplication by a rational scalar as an additive endomorphism of `K`. -/
def fieldScalarAddHom (q : K) : K →+ K :=
  DistribSMul.toAddMonoidHom K q
