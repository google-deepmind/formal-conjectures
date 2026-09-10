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

public import FormalConjecturesForMathlib.AlgebraicGeometry.SmoothClosedSupportCoclassSection
public import FormalConjecturesForMathlib.AlgebraicGeometry.CycleComponentSmoothSupportPurity
public import FormalConjecturesForMathlib.AlgebraicTopology.SupportRelativeCohomologyOpenTransport

/-!
# The normalized component coclass on the original ambient smooth-support open

The component's actual smooth locus is closed in the complement of its singular
boundary. We construct its exactly normalized smooth-support section there and
transport it through the actual analytic open embedding. The result is a section
of the ORIGINAL ambient relative-cohomology sheaf on the singular-boundary
complement. No section, purity comparison, or orientation coherence is an input.
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

/-- The constructed normalized smooth-support section transported to an actual
larger ambient space through an open embedding. -/
def smoothClosedSupportOpenImageCoclassSection :
  (supportRelativeCohomologySheaf M S (2 * (d - m))).obj.obj (op (hf.functor.obj ⊤)) :=
  supportRelativeCohomologySectionOpenImage f hf S (Set.range (Point.map i)) hS
    (2 * (d - m)) (smoothClosedSupportCoclassSection X Y i m d)

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

/-- The actual structure morphism of the closed-lift source. -/
abbrev cycleComponentSmoothClosedLiftStructureMap :=
  (cycleComponentSmoothLocusOver X x).hom

include hx in
/-- The proved dimension of the actual closed-lift source. -/
theorem cycleComponentSmoothClosedLiftStructureMap_smoothOfRelativeDimension :
    SmoothOfRelativeDimension (d - p) (cycleComponentSmoothClosedLiftStructureMap X x) :=
  cycleComponentSmoothLocus_smoothOfRelativeDimension X x (d := d) hx

include X hx in
omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- The codimension arithmetic is proved from the actual coheight bound. -/
theorem cycleComponentSmoothClosedLift_codimension :
    d - (d - p) = p := by
  have h := SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) (d := d) x
  rw [hx] at h
  have hpd : p ≤ d := by exact_mod_cast h
  omega

/-- The normalized section in the auxiliary algebraic ambient open, in the proved
degree 2p. The class is the general normal-chart gluing, not supplied data. -/
def cycleComponentSmoothClosedLiftCoclassSection :
    (supportRelativeCohomologySheaf
      (TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)))
      (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
      (2 * p)).obj.obj (op ⊤) := by
  let := cycleComponentSmoothClosedLiftStructureMap_smoothOfRelativeDimension X x (d := d) hx
  have hdeg := cycleComponentSmoothClosedLift_codimension X x (d := d) hx
  exact hdeg ▸ smoothClosedSupportCoclassSection
    (cycleComponentSmoothLocusAmbientOpenOver X x)
    (cycleComponentSmoothLocusOver X x)
    (cycleComponentSmoothLocusClosedLiftOver X x) (d - p) d

/-- The actual analytic open-embedding map back to the original ambient space. -/
def cycleComponentSmoothClosedLiftAmbientMap :
    TopCat.of (ComplexPoint (cycleComponentSmoothLocusAmbientOpenOver X x)) ⟶
    TopCat.of (ComplexPoint X) :=
  TopCat.ofHom (Point.continuousMap
    (openInclusion X (cycleComponentSmoothLocusAmbientOpen X x)))

omit [IsIntegral X.left] [Smooth X.hom] in
theorem cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding :
    IsOpenEmbedding (cycleComponentSmoothClosedLiftAmbientMap X x) :=
  isOpenEmbedding_map_open X (cycleComponentSmoothLocusAmbientOpen X x)

/-- Support membership is transported by the actual lift-image theorem. -/
theorem cycleComponentSmoothClosedLiftAmbientMap_support :
    cycleComponentSmoothClosedLiftAmbientMap X x ⁻¹' cycleComponentSupport X x =
      Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)) :=
  (cycleComponentSmoothLocusClosedLift_complexPoints_range X x).symm

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The image open is exactly the complement of the canonical first singular boundary. -/
theorem cycleComponentSmoothClosedLiftAmbientMap_imageOpen :
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x).functor.obj ⊤ =
      cycleComponentSmoothSupportAmbientOpen X x := by
  apply Opens.ext
  change (cycleComponentSmoothClosedLiftAmbientMap X x) '' Set.univ = _
  rw [Set.image_univ]
  exact cycleComponentSmoothLocusAmbientOpen_analytic_image X x

/-- The actual normalized component coclass section, living on the singular-boundary
complement in the ORIGINAL ambient relative-cohomology sheaf. -/
def cycleComponentSmoothSupportCoclassSection :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * p)).obj.obj
      (op (cycleComponentSmoothSupportAmbientOpen X x)) :=
  supportRelativeCohomologySectionOnOpen (cycleComponentSmoothClosedLiftAmbientMap X x)
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
    (cycleComponentSupport X x)
    (Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)))
    (cycleComponentSmoothClosedLiftAmbientMap_support X x)
    (2 * p) (cycleComponentSmoothSupportAmbientOpen X x)
    (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x)
    (cycleComponentSmoothClosedLiftCoclassSection X x (d := d) hx)

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
