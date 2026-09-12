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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.CycleComponentSmoothSupportCoclassSection

/-!
# The normalized component coclass on the original ambient smooth-support open

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.CycleComponentSmoothSupportCoclassSection`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

section GeneralOpenTransport

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]
  {M : TopCat.{0}} (f : TopCat.of (ComplexPoint X) ⟶ M)
  (hf : IsOpenEmbedding f) (S : Set M)
  (hS : f ⁻¹' S = Set.range (Point.map i))

/-- On every transported chart, the section is precisely the unit image of the
actual transported normal-projection coclass. This displays exact normalization. -/
theorem smoothClosedSupportOpenImageCoclassSection_restrict_chart
    (z : ComplexPoint Y) :
    (supportRelativeCohomologySheaf M S (2 * (d - m))).obj.map
      (hf.functor.map (homOfLE (show
        smoothClosedSupportChartOpen X Y i m d z ≤ ⊤ from le_top))).op
      (smoothClosedSupportOpenImageCoclassSection X Y i m d f hf S hS) =
    (supportRelativeCohomologyToSheaf M S (2 * (d - m))).app
      (op (hf.functor.obj (smoothClosedSupportChartOpen X Y i m d z)))
      ((supportRelativeCohomologyPresheafOpenIso f hf S (Set.range (Point.map i)) hS
          (2 * (d - m))).inv.app (op (smoothClosedSupportChartOpen X Y i m d z))
        (smoothClosedSupportChartCoclass X Y i m d z
          (smoothClosedSupportChartOpen X Y i m d z) (le_refl _))) := by
  rw [smoothClosedSupportOpenImageCoclassSection,
    supportRelativeCohomologySectionOpenImage_restrict,
    smoothClosedSupportCoclassSection_restrict_chart]
  exact supportRelativeCohomologySheafOpenIso_unit_apply f hf S (Set.range (Point.map i))
    hS (2 * (d - m)) (smoothClosedSupportChartOpen X Y i m d z) _

end GeneralOpenTransport

section Component

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {d p : ℕ} [SmoothOfRelativeDimension d X.hom] (hx : Order.coheight x = p)

/-- Restriction to each actual image neighborhood agrees with transport of the
constructed auxiliary normalized section. No ambient section comparison is supplied. -/
theorem cycleComponentSmoothSupportCoclassSection_restrict
    (V : Opens (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)))
    (hV : (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x).functor.obj V ≤
      cycleComponentSmoothSupportAmbientOpen X x) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * p)).obj.map (homOfLE hV).op
        (cycleComponentSmoothSupportCoclassSection X x (d := d) hx) =
    (supportRelativeCohomologySheafOpenIso (cycleComponentSmoothClosedLiftAmbientMap X x)
      (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
      (cycleComponentSupport X x)
      (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
      (cycleComponentSmoothClosedLiftAmbientMap_support X x) (2 * p)).hom.hom.app (op V)
      ((supportRelativeCohomologySheaf
        (TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)))
        (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
        (2 * p)).obj.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (cycleComponentSmoothClosedLiftCoclassSection X x (d := d) hx)) :=
  supportRelativeCohomologySectionOnOpen_restrict
    (cycleComponentSmoothClosedLiftAmbientMap X x)
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
    (cycleComponentSupport X x)
    (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
    (cycleComponentSmoothClosedLiftAmbientMap_support X x)
    (2 * p) (cycleComponentSmoothSupportAmbientOpen X x)
    (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x)
    (cycleComponentSmoothClosedLiftCoclassSection X x (d := d) hx) V hV

end Component

end AlgebraicGeometry.ComplexPoint
