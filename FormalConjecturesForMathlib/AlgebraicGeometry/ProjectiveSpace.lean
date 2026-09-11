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
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

import FormalConjecturesForMathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Projective space and explicit projective presentations

This file constructs projective space over a scheme as a pullback from `Proj`, proves its
structure morphism proper for finitely many homogeneous coordinates, and packages a closed
embedding into finite-dimensional projective space as an explicit projective presentation.

The original projective-space construction was contributed to Mathlib in
[`mathlib4` pull request #26061](https://github.com/leanprover-community/mathlib4/pull/26061).
-/

@[expose] public section

-- The contents of this file will be in mathlib as of #26061

universe u v
open CategoryTheory Limits MvPolynomial AlgebraicGeometry

variable (n : Type v) (S : Scheme.{max u v})

local notation "ℤ[" n "]" => homogeneousSubmodule n ℤ
local notation3 "ℤ[" n "].{" u "," v "}" => homogeneousSubmodule n (ULift.{max u v} ℤ)

attribute [local instance] MvPolynomial.gradedAlgebra

/--
The projective space over a scheme `S`, with homogeneous coordinates indexed by `n`
-/
noncomputable def ProjectiveSpace : Scheme.{max u v} :=
  pullback (terminal.from S) (terminal.from (Proj ℤ[n].{u, v}))

/-- `ℙ(n; S)` is projective space over `S` with homogeneous coordinates indexed by `n`. -/
scoped [AlgebraicGeometry] notation "ℙ("n"; "S")" => ProjectiveSpace n S

namespace ProjectiveSpace

/-- The degree-zero part of the standard grading on a polynomial ring consists exactly of
the constant polynomials. -/
noncomputable def degreeZeroEquiv (R : Type*) [CommRing R] :
    homogeneousSubmodule n R 0 ≃+* R where
  toFun f := coeff 0 f.1
  invFun r := ⟨C r, isHomogeneous_C n r⟩
  left_inv f := Subtype.ext (totalDegree_eq_zero_iff_eq_C.mp
    ((totalDegree_zero_iff_isHomogeneous n).mpr f.2)).symm
  right_inv r := coeff_zero_C r
  map_mul' x y := by
    have hx := totalDegree_eq_zero_iff_eq_C.mp
      ((totalDegree_zero_iff_isHomogeneous n).mpr x.2)
    have hy := totalDegree_eq_zero_iff_eq_C.mp
      ((totalDegree_zero_iff_isHomogeneous n).mpr y.2)
    change coeff 0 (x.1 * y.1) = coeff 0 x.1 * coeff 0 y.1
    rw [hx, hy, ← map_mul, coeff_zero_C, coeff_zero_C, coeff_zero_C]
  map_add' _ _ := rfl

/-- A polynomial ring in finitely many variables is of finite type over its degree-zero
homogeneous subring. -/
noncomputable instance degreeZeroFiniteType [Finite n] (R : Type*) [CommRing R] :
    Algebra.FiniteType (homogeneousSubmodule n R 0) (MvPolynomial n R) := by
  rw [← RingHom.finiteType_algebraMap]
  have hC : (C : R →+* MvPolynomial n R).FiniteType := by
    rw [← MvPolynomial.algebraMap_eq]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have he : (degreeZeroEquiv n R).toRingHom.FiniteType :=
    RingHom.FiniteType.of_surjective _ (degreeZeroEquiv n R).surjective
  have h := hC.comp he
  convert h using 1
  exact RingHom.ext fun x ↦ totalDegree_eq_zero_iff_eq_C.mp
    ((totalDegree_zero_iff_isHomogeneous n).mpr x.2)

/-- Projective space on finitely many homogeneous coordinates is proper over the terminal
scheme. -/
noncomputable instance terminalProjProper [Finite n] :
    IsProper (terminal.from (Proj ℤ[n].{u, v})) := by
  have hterminal : IsTerminal
      (Spec ↧(homogeneousSubmodule n (ULift.{max u v} ℤ) 0)) :=
    IsTerminal.ofIso specULiftZIsTerminal
      (Scheme.Spec.mapIso
        (degreeZeroEquiv n (ULift.{max u v} ℤ)).toCommRingCatIso.op)
  have := isIso_of_isTerminal hterminal terminalIsTerminal (terminal.from _)
  rw [← terminal.comp_from (Proj.toSpecZero ℤ[n].{u, v}),
    MorphismProperty.cancel_right_of_respectsIso (P := @IsProper)]
  infer_instance

/-- The structure morphism from projective space to its base scheme. -/
noncomputable def toBase : ProjectiveSpace n S ⟶ S :=
  pullback.fst (terminal.from S) (terminal.from (Proj ℤ[n].{u, v}))

/-- Finite-dimensional projective space is proper over its base. -/
noncomputable instance toBaseProper [Finite n] : IsProper (toBase n S) := by
  change IsProper (pullback.fst (terminal.from S) (terminal.from (Proj ℤ[n].{u, v})))
  infer_instance

universe w

variable {X T : Scheme.{w}}

/-- An explicit closed embedding over `S` into a finite-dimensional projective space. -/
structure Presentation (f : X ⟶ T) where
  /-- The dimension of the ambient projective space. -/
  ambientDimension : ℕ
  /-- The closed embedding into projective space. -/
  immersion : X ⟶ ProjectiveSpace (Fin (ambientDimension + 1)) T
  [isClosedImmersion : IsClosedImmersion immersion]
  /-- The embedding is a morphism over the base scheme. -/
  immersion_toBase :
    immersion ≫ toBase (Fin (ambientDimension + 1)) T = f

end ProjectiveSpace

namespace AlgebraicGeometry

open ProjectiveSpace

universe w

variable {X T : Scheme.{w}}

/-- A scheme morphism is projective if it admits a finite-dimensional projective presentation. -/
class IsProjective (f : X ⟶ T) : Prop where
  /-- A finite-dimensional projective presentation exists. -/
  nonempty_presentation : Nonempty (Presentation f)

/-- A projective morphism in the explicit-presentation sense is proper. -/
instance IsProjective.isProper {f : X ⟶ T} [h : IsProjective f] : IsProper f := by
  obtain ⟨P⟩ := h.nonempty_presentation
  let : IsClosedImmersion P.immersion := P.isClosedImmersion
  have hcomp : IsProper
      (P.immersion ≫ toBase (Fin (P.ambientDimension + 1)) T) := by
    infer_instance
  rwa [P.immersion_toBase] at hcomp

end AlgebraicGeometry
