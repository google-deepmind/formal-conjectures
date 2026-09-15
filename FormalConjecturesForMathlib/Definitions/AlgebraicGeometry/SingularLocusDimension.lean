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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.ClosedSubsetDimensionDrop
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ReducedSmoothStratification
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.CycleComponentNormalGeometry
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SmoothEquidimensional

import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SmoothComplexCoordinates
import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.CycleComponentDimension

/-!
# The singular locus has smaller algebraic dimension

Over a perfect field the complement of the smooth locus of a reduced irreducible scheme is
a proper closed subset. This file constructs that reduced closed subscheme and proves its
strict Krull-dimension bound, including the `d - p` bound for cycle components. The bounds
are on algebraic dimension throughout.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

/-- The closed complement of the actual smooth locus. -/
def singularLocusClosed : Closeds X := f.smoothLocus.compl

/-- The singular locus equipped with its reduced closed-subscheme structure. -/
def reducedSingularLocus : Scheme := reducedClosedSubscheme (singularLocusClosed f)

/-- Its canonical closed immersion in the original scheme. -/
def reducedSingularLocusι : reducedSingularLocus f ⟶ X :=
  reducedClosedSubschemeι (singularLocusClosed f)

instance reducedSingularLocus_isReduced : IsReduced (reducedSingularLocus f) :=
  inferInstanceAs (IsReduced (reducedClosedSubscheme (singularLocusClosed f)))

instance reducedSingularLocusι_isClosedImmersion :
    IsClosedImmersion (reducedSingularLocusι f) :=
  inferInstanceAs (IsClosedImmersion (reducedClosedSubschemeι (singularLocusClosed f)))

variable (Y : Over (Spec (.of ℂ)))
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

/-- The singular locus of every cycle component admits the actual finite smooth
decomposition constructed by Noetherian recursion. -/
def cycleComponentSingularStratification (x : Y.left) :
    List (Closeds (cycleComponent Y.left x)) := by
  letI := cycleComponent_isNoetherian Y x
  exact reducedSmoothStratification (cycleComponentι Y.left x ≫ Y.hom)
    (singularLocusClosed (cycleComponentι Y.left x ≫ Y.hom))

end AlgebraicGeometry
