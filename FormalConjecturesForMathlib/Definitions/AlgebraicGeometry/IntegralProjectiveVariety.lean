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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.Points
import FormalConjecturesForMathlib.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Integral projective complex varieties

An integral projective complex variety bundles an integral scheme with a projective structure
morphism to `Spec ℂ`. Such a scheme is Noetherian, since a projective morphism is of finite type
and quasi-compact.

The bundled form exists so that the point and analytification constructions of
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.Points` can be applied to it without repeating
the hypotheses: `over` produces the object over `Spec ℂ` that those constructions expect.
-/

@[expose] public section

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- An integral projective algebraic variety over `ℂ`. Projectivity is witnessed by an explicit
closed embedding into a finite-dimensional projective space. -/
structure IntegralProjectiveComplexVariety where
  /-- The underlying scheme. -/
  scheme : Scheme
  [isIntegral : IsIntegral scheme]
  /-- The structure morphism to `Spec ℂ`. -/
  structureMap : scheme ⟶ Spec ↧ℂ
  [projective : IsProjective structureMap]

/-- A projective complex scheme is Noetherian. -/
theorem isNoetherian_of_isProjective (X : Over (Spec ↧ℂ))
    [IsProjective X.hom] : IsNoetherian X.left where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace X.hom

namespace IntegralProjectiveComplexVariety

/-- The integral structure carried by an integral projective complex variety. -/
instance (V : IntegralProjectiveComplexVariety) : IsIntegral V.scheme := V.isIntegral

/-- The projective presentation carried by an integral projective complex variety. -/
instance (V : IntegralProjectiveComplexVariety) :
    IsProjective V.structureMap := V.projective

/-- An integral projective complex variety is Noetherian. -/
noncomputable instance (V : IntegralProjectiveComplexVariety) : IsNoetherian V.scheme :=
  @isNoetherian_of_isProjective (Over.mk V.structureMap) V.projective

/-- The variety regarded as the corresponding object over `Spec ℂ`. -/
noncomputable abbrev over (V : IntegralProjectiveComplexVariety) : Over (Spec ↧ℂ) :=
  Over.mk V.structureMap

/-- The complex points of an integral projective complex variety. -/
abbrev analyticPoint (V : IntegralProjectiveComplexVariety) :=
  ComplexPoint V.over

noncomputable instance (V : IntegralProjectiveComplexVariety) :
    TopologicalSpace V.analyticPoint :=
  Point.analyticTopology

/-- The analytification as a topological space. -/
noncomputable def analytification (V : IntegralProjectiveComplexVariety) : TopCat :=
  complexAnalytification.obj V.over

end IntegralProjectiveComplexVariety

end AlgebraicGeometry
