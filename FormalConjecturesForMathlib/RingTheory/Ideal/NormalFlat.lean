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

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Normal flatness along an ideal

The degree `n` piece of the associated graded module of an ideal `I` is
`I ^ n / I ^ (n + 1)`. We represent it as `I ^ n / I • ⊤`, so it carries the
canonical module structure over `R ⧸ I`. Normal flatness means that all these
pieces are flat over `R ⧸ I`.

*References:*
* [Stacks, the normal cone of an immersion](https://stacks.math.columbia.edu/tag/062Z).
* [Cossart--Piltant, Resolution of singularities of arithmetical
  threefolds](https://arxiv.org/abs/1412.0868), Remark 1.4.
-/

@[expose] public section

namespace Ideal

universe u

variable {R : Type u} [CommRing R]

/-- The module `I ^ n / I ^ (n + 1)`, with its natural `R ⧸ I`-module structure. -/
def AdicGradedPiece (I : Ideal R) (n : ℕ) : Type u :=
  ↥(I ^ n) ⧸ (I • ⊤ : Submodule R ↥(I ^ n))
deriving AddCommGroup, Module R, Module (R ⧸ I)

/-- The denominator in `AdicGradedPiece I n`, viewed in `R`, is `I ^ (n + 1)`. -/
theorem map_adicGradedPiece_denominator (I : Ideal R) (n : ℕ) :
    Submodule.map (I ^ n).subtype (I • ⊤ : Submodule R ↥(I ^ n)) = I ^ (n + 1) := by
  rw [Submodule.map_smul'', Submodule.map_subtype_top, smul_eq_mul, pow_succ']

/-- The affine scheme `Spec R` is normally flat along the closed subscheme defined by `I`. -/
def IsNormallyFlat (I : Ideal R) : Prop :=
  ∀ n : ℕ, Module.Flat (R ⧸ I) (I.AdicGradedPiece n)

/-- Normal flatness at a closed point is automatic: the graded pieces are vector spaces. -/
theorem isNormallyFlat_of_isMaximal (I : Ideal R) [I.IsMaximal] : I.IsNormallyFlat := by
  let := Ideal.Quotient.field I
  intro n
  infer_instance

end Ideal
