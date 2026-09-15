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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ClosedImmersionComplexPoint
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ProjectiveAnalytification

import FormalConjecturesForMathlib.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Analytic compactness of a projective complex scheme

A projective presentation of a complex scheme is a closed immersion into scheme-theoretic
projective space. On complex points it therefore induces a closed topological embedding into the
complex points of projective space, which are analytically compact.

Consequently the analytic complex points of any projective complex scheme form a compact space.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace Topology

namespace AlgebraicGeometry

namespace ComplexPoint

open Point

/-- A complex point of finite-dimensional scheme-theoretic projective space is determined by its
underlying closed point. -/
lemma projectiveSpace_underlying_injective (n : ℕ) :
    Function.Injective
      (@underlying ℂ _ _
        (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) :=
  @underlying_injective_of_locallyOfFiniteType
    (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))
    (inferInstanceAs (LocallyOfFiniteType
      (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))))

end ComplexPoint

namespace ProjectiveSpace.Presentation

/-- The immersion of a projective presentation, bundled over the complex base. -/
noncomputable abbrev overImmersion {X : Scheme} {f : X ⟶ Spec ↧ℂ}
    (P : ProjectiveSpace.Presentation f) :
    Over.mk f ⟶
      Over.mk (ProjectiveSpace.toBase (Fin (P.ambientDimension + 1)) (Spec ↧ℂ)) :=
  Over.homMk P.immersion P.immersion_toBase

/-- The continuous map on complex points induced by an explicit projective presentation. -/
noncomputable def analyticImmersion {X : Scheme} {f : X ⟶ Spec ↧ℂ}
    (P : ProjectiveSpace.Presentation f) :
    @ContinuousMap (ComplexPoint (Over.mk f))
      (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (P.ambientDimension + 1)) (Spec ↧ℂ))))
      Point.analyticTopology Point.analyticTopology :=
  Point.continuousMap (overImmersion P)

/-- The analytic map of an explicit projective presentation is injective. -/
lemma analyticImmersion_injective {X : Scheme} {f : X ⟶ Spec ↧ℂ}
    (P : ProjectiveSpace.Presentation f) : Function.Injective (analyticImmersion P) := by
  let : IsClosedImmersion P.immersion := P.isClosedImmersion
  exact ComplexPoint.map_injective_of_mono (overImmersion P)

/-- The analytic map of an explicit projective presentation is a closed topological
embedding. -/
lemma analyticImmersion_isClosedEmbedding {X : Scheme} {f : X ⟶ Spec ↧ℂ}
    (P : ProjectiveSpace.Presentation f) :
    @IsClosedEmbedding (ComplexPoint (Over.mk f))
      (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (P.ambientDimension + 1)) (Spec ↧ℂ))))
      Point.analyticTopology Point.analyticTopology (analyticImmersion P) := by
  let : IsClosedImmersion P.immersion := P.isClosedImmersion
  let : IsClosedImmersion (overImmersion P).left := P.isClosedImmersion
  exact ComplexPoint.isClosedEmbedding_map_of_closedImmersion (overImmersion P)

/-- The analytic complex points of an explicit projective presentation form a compact space. -/
theorem complexPoint_compactSpace {X : Scheme} {f : X ⟶ Spec ↧ℂ}
    (P : ProjectiveSpace.Presentation f) :
    @CompactSpace (ComplexPoint (Over.mk f)) Point.analyticTopology := by
  let : TopologicalSpace (ComplexPoint (Over.mk f)) := Point.analyticTopology
  exact (analyticImmersion_isClosedEmbedding P).compactSpace

end ProjectiveSpace.Presentation

namespace IsProjective

/-- The analytic complex points of a projective complex scheme form a compact space. -/
noncomputable instance complexPoint_compactSpace {X : Over (Spec ↧ℂ)}
    [h : IsProjective X.hom] : CompactSpace (ComplexPoint X) :=
  ProjectiveSpace.Presentation.complexPoint_compactSpace
    (Classical.choice h.nonempty_presentation)

end IsProjective

end AlgebraicGeometry
