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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.CycleComponentSmoothClosedLift

/-!
# The actual smooth-locus closed lift of an integral cycle component

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.CycleComponentSmoothClosedLift`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)

/-- The target is the actual source-open target of the smooth locus. -/
theorem cycleComponentSmoothLocusAmbientOpen_eq_sourceOpenTarget :
    cycleComponentSmoothLocusAmbientOpen X x =
      closedImmersionSourceOpenTarget (cycleComponentι X.left x)
        (cycleComponentι X.left x ≫ X.hom).smoothLocus := rfl

/-- The exact image of the lift is the restriction of the full component support. -/
theorem range_cycleComponentSmoothLocusClosedLift :
    Set.range (cycleComponentSmoothLocusClosedLift X x) =
      (cycleComponentSmoothLocusAmbientOpen X x).ι ⁻¹' closure ({x} : Set X.left) := by
  rw [← range_cycleComponentι X.left x]
  exact range_closedImmersionSourceOpenLift _ _

variable {d p : ℕ} [SmoothOfRelativeDimension d X.hom]

/-- The smooth locus has exactly the constant relative dimension of the integral
component, not just a locally chosen dimension. -/
theorem cycleComponentSmoothLocus_smoothOfRelativeDimension (hx : Order.coheight x = p) :
    SmoothOfRelativeDimension (d - p)
      ((cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫ cycleComponentι X.left x ≫ X.hom) := by
  let A := (cycleComponentι X.left x ≫ X.hom).smoothLocus
  let g := A.ι ≫ cycleComponentι X.left x ≫ X.hom
  let : Smooth g := cycleComponent_smoothLocus_smooth X x
  let : IsIntegral A := cycleComponent_smoothLocus_isIntegral X x
  obtain ⟨m, hm⟩ := Smooth.exists_smoothOfRelativeDimension g
  let : SmoothOfRelativeDimension m g := hm
  obtain ⟨z, hzA, hzClosed⟩ := (dense_cycleComponent_smooth_closedPoints X x).nonempty
  let zA : A.toScheme := ⟨z, hzA⟩
  have hzAClosed : IsClosed ({zA} : Set A) := by
    have he : A.ι ⁻¹' ({z} : Set (cycleComponent X.left x)) = {zA} := by
      ext a
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    exact he ▸ hzClosed.preimage A.ι.continuous
  have hmEq : m = d - p := by
    exact_mod_cast calc
      (m : ℕ∞) = Order.coheight zA :=
        (SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
          (f := g) (d := m) zA hzAClosed).symm
      _ = Order.coheight z := (coheight_eq_of_isOpenImmersion (x := zA) A.ι).symm
      _ = d - p := cycleComponent_closedPoint_coheight_eq_sub X x z hx hzClosed
  subst m
  exact hm

namespace ComplexPoint

attribute [local instance] cycleComponentSmoothClosedLiftAnalyticTopology

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The analytic image of the algebraic boundary complement is the exact open used by
the original ambient supported resolution. -/
theorem cycleComponentSmoothLocusAmbientOpen_analytic_image :
    Set.range (Point.map (openInclusion X (cycleComponentSmoothLocusAmbientOpen X x))) =
      ((cycleComponentSingularAnalyticClosedFiltration X x 0).compl : Set (ComplexPoint X)) := by
  rw [range_map_of_isImmersion X]
  change (Point.underlying : ComplexPoint X → X.left) ⁻¹'
      Set.range (cycleComponentSmoothLocusAmbientOpen X x).ι = _
  rw [Scheme.Opens.range_ι]
  rfl

/-- The complex-point image of the closed lift is precisely the restricted full support. -/
theorem cycleComponentSmoothLocusClosedLift_complexPoints_range :
    Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)) =
      Point.map (openInclusion X (cycleComponentSmoothLocusAmbientOpen X x)) ⁻¹'
          (cycleComponentSupport X x) := by
  rw [range_map_of_isImmersion]
  change (Point.underlying : ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x) →
    (cycleComponentSmoothLocusAmbientOpenOver X x).left) ⁻¹'
      Set.range (cycleComponentSmoothLocusClosedLift X x) = _
  rw [range_cycleComponentSmoothLocusClosedLift]
  rfl

end ComplexPoint
end AlgebraicGeometry
