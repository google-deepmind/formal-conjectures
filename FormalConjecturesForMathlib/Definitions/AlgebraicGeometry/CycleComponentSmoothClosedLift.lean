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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.CycleComponentSingularClosedFiltration
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ClosedImmersionSourceOpen
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.CycleComponentClosedPointDimension

/-!
# The smooth-locus closed lift of an integral cycle component

The ambient open is the complement of the first canonical singular-boundary support, and
the smooth locus embeds closed in it. Its constant relative dimension is `d-p`, by smooth
equidimensionality together with the coheight formula for a closed point of the integral
component.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)

/-- The precise algebraic open complementary to the canonical singular boundary. -/
def cycleComponentSmoothLocusAmbientOpen : X.left.Opens :=
  (cycleComponentSingularAmbientClosedFiltration X x 0).compl

/-- The ambient boundary complement with its induced structure map to `Spec ℂ`. -/
abbrev cycleComponentSmoothLocusAmbientOpenOver : Over (Spec (.of ℂ)) :=
  ComplexPoint.openScheme X (cycleComponentSmoothLocusAmbientOpen X x)

instance cycleComponentSmoothLocusAmbientOpenOver_locallyOfFiniteType :
    LocallyOfFiniteType (cycleComponentSmoothLocusAmbientOpenOver X x).hom := by
  change LocallyOfFiniteType ((cycleComponentSmoothLocusAmbientOpen X x).ι ≫ X.hom)
  infer_instance

instance cycleComponentSmoothLocusAmbientOpenInclusion_isImmersion :
    IsImmersion
      (ComplexPoint.openInclusion X (cycleComponentSmoothLocusAmbientOpen X x)).left := by
  change IsImmersion (cycleComponentSmoothLocusAmbientOpen X x).ι
  infer_instance

/-- The actual smooth locus, closed in the complement of its singular boundary. -/
def cycleComponentSmoothLocusClosedLift :
    (cycleComponentι X.left x ≫ X.hom).smoothLocus.toScheme ⟶
      (cycleComponentSmoothLocusAmbientOpen X x).toScheme :=
  closedImmersionSourceOpenLift (cycleComponentι X.left x) (cycleComponentι X.left x ≫ X.hom).smoothLocus

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
instance cycleComponentSmoothLocusClosedLift_isClosedImmersion :
    IsClosedImmersion (cycleComponentSmoothLocusClosedLift X x) := by
  dsimp [cycleComponentSmoothLocusClosedLift]
  infer_instance

@[reassoc (attr := simp)]
theorem cycleComponentSmoothLocusClosedLift_ι :
    cycleComponentSmoothLocusClosedLift X x ≫ (cycleComponentSmoothLocusAmbientOpen X x).ι =
      (cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫ cycleComponentι X.left x :=
  closedImmersionSourceOpenLift_ι _ _

/-- The smooth-locus closed lift bundled over `Spec ℂ`. -/
def cycleComponentSmoothLocusClosedLiftOver :
    ComplexPoint.cycleComponentSmoothLocusOver X x ⟶
      cycleComponentSmoothLocusAmbientOpenOver X x :=
  Over.homMk (cycleComponentSmoothLocusClosedLift X x) (by
    change cycleComponentSmoothLocusClosedLift X x ≫
      ((cycleComponentSmoothLocusAmbientOpen X x).ι ≫ X.hom) =
        ((cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
          cycleComponentι X.left x) ≫ X.hom
    rw [← Category.assoc, cycleComponentSmoothLocusClosedLift_ι])

instance cycleComponentSmoothLocusClosedLiftOver_isClosedImmersion :
    IsClosedImmersion (cycleComponentSmoothLocusClosedLiftOver X x).left := by
  change IsClosedImmersion (cycleComponentSmoothLocusClosedLift X x)
  infer_instance

variable {d p : ℕ} [SmoothOfRelativeDimension d X.hom]

/-- The ambient open retains the original smooth relative dimension. -/
instance cycleComponentSmoothLocusAmbientOpen_smoothOfRelativeDimension :
    SmoothOfRelativeDimension d ((cycleComponentSmoothLocusAmbientOpen X x).ι ≫ X.hom) := by
  simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d
    (cycleComponentSmoothLocusAmbientOpen X x).ι X.hom

instance cycleComponentSmoothLocusAmbientOpenOver_smoothOfRelativeDimension :
    SmoothOfRelativeDimension d (cycleComponentSmoothLocusAmbientOpenOver X x).hom := by
  change SmoothOfRelativeDimension d
    ((cycleComponentSmoothLocusAmbientOpen X x).ι ≫ X.hom)
  infer_instance

namespace ComplexPoint

local instance cycleComponentSmoothClosedLiftAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- The full cycle support as an actual closed analytic subset. -/
def cycleComponentAnalyticClosedSupport : Closeds (ComplexPoint X) :=
  ⟨cycleComponentSupport X x, isClosed_cycleComponentSupport X x⟩

end ComplexPoint
end AlgebraicGeometry
