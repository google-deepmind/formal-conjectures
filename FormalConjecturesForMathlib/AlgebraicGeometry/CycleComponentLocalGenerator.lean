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

public import FormalConjecturesForMathlib.AlgebraicTopology.ChartLocalFundamentalClass
public import FormalConjecturesForMathlib.AlgebraicGeometry.CycleComponentNormalCoordinates

import FormalConjecturesForMathlib.AlgebraicGeometry.ProjectiveAnalytificationHausdorff
import FormalConjecturesForMathlib.AlgebraicTopology.ChartLocalFundamentalClassGenerator
import FormalConjecturesForMathlib.AlgebraicTopology.LocalFundamentalClassGenerator
import FormalConjecturesForMathlib.AlgebraicTopology.PuncturedEuclideanFundamentalClass

/-!
# Local generators from exact cycle-component coordinates

An exact étale coordinate package on the smooth locus of a cycle component gives an actual
analytic chart on its chosen affine neighborhood. This file constructs that chart directly from
the retained polynomial-ring homomorphism. It then transports the proved standard complex local
homology generator through the chart.

The chart map factors through its open target and the proved point-neighborhood excision theorem.
Consequently the resulting class generates the full local homology of the affine component
neighborhood. This file does not construct a supported cohomology class or prove purity for the
component inside the ambient variety.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicGeometry

attribute [local instance] overSpecAlgebra

noncomputable local instance {Y : Over (Spec ↧ℂ)} :
    TopologicalSpace (ComplexPoint Y) := Point.analyticTopology

variable {d n : ℕ} {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom] {x : X.left}
  [SmoothOfRelativeDimension d X.hom]

namespace CycleComponentSeparateLocalCoordinates

variable (C : CycleComponentSeparateLocalCoordinates X x d n)
/-- The selected smooth component point regarded as a complex point of the smooth locus. -/
def smoothPoint : ComplexPoint (componentSmoothScheme X x) :=
  ComplexPoint.asOpenPoint (Over.mk (cycleComponentι X.left x ≫ X.hom))
    (componentSmoothLocus X x)
    C.point C.point_mem_smoothLocus

/-- The complex structure map on the selected affine component neighborhood. -/
abbrev neighborhoodStructureMap :
    C.componentNeighborhood.toScheme ⟶ Spec ↧ℂ :=
  C.componentNeighborhood.ι ≫ componentSmoothStructureMap X x

/-- The selected affine component neighborhood, bundled over the complex base. -/
abbrev neighborhoodScheme : Over (Spec ↧ℂ) :=
  Over.mk C.neighborhoodStructureMap

/-- The selected smooth point regarded as a complex point of its affine neighborhood. -/
def neighborhoodPoint :
    ComplexPoint C.neighborhoodScheme :=
  ComplexPoint.asOpenPoint (componentSmoothScheme X x) C.componentNeighborhood
    (smoothPoint C) (by
      change (smoothPoint C).underlying ∈ C.componentNeighborhood
      have hmap : Point.map (ComplexPoint.openInclusion (Over.mk (cycleComponentι X.left x ≫ X.hom))
          (componentSmoothLocus X x)) (smoothPoint C) =
          C.point :=
        congrArg Subtype.val
          ((ComplexPoint.openEquiv (Over.mk (cycleComponentι X.left x ≫ X.hom))
            (componentSmoothLocus X x)).apply_symm_apply
              ⟨C.point, C.point_mem_smoothLocus⟩)
      have hu := congrArg Point.underlying hmap
      rw [Point.underlying_map] at hu
      have hu' : (smoothPoint C).underlying =
          (⟨C.point.underlying, C.point_mem_smoothLocus⟩ :
            (componentSmoothLocus X x).toScheme) := Subtype.ext hu
      rw [hu']
      exact C.point_mem_componentNeighborhood)

/-- The retained exact component coordinates, transported to global sections of the affine
neighborhood itself. -/
def coordinateRingHomOnNeighborhood :
    MvPolynomial (Fin n) ℂ →+* Γ(C.componentNeighborhood.toScheme, ⊤) :=
  C.componentNeighborhood.topIso.inv.hom.comp C.componentCoordinateAlgHom.toRingHom

/-- The transported coordinate map is compatible with the neighborhood's complex structure
map. -/
lemma C_comp_coordinateRingHomOnNeighborhood :
    CommRingCat.ofHom MvPolynomial.C ≫
        CommRingCat.ofHom C.coordinateRingHomOnNeighborhood =
      (Scheme.ΓSpecIso ↧ℂ).inv ≫ C.neighborhoodStructureMap.appTop := by
  apply (cancel_mono C.componentNeighborhood.topIso.hom).mp
  change (((CommRingCat.ofHom MvPolynomial.C) ≫
      CommRingCat.ofHom C.componentCoordinateAlgHom.toRingHom) ≫
        C.componentNeighborhood.topIso.inv) ≫
          C.componentNeighborhood.topIso.hom =
    (((Scheme.ΓSpecIso ↧ℂ).inv ≫
      C.neighborhoodStructureMap.appTop) ≫
        C.componentNeighborhood.topIso.hom)
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [neighborhoodStructureMap, Scheme.Hom.comp_appTop, Category.assoc]
  rw [Scheme.Opens.ι_appTop_topIso_hom]
  change CommRingCat.ofHom
      (C.componentCoordinateAlgHom.toRingHom.comp MvPolynomial.C) =
    CommRingCat.ofHom
      (algebraMap ℂ Γ((componentSmoothScheme X x).left,
        C.componentNeighborhood))
  exact congrArg CommRingCat.ofHom C.componentCoordinateAlgHom.comp_algebraMap

/-- The transported exact coordinate map remains étale. -/
lemma coordinateRingHomOnNeighborhood_etale :
    C.coordinateRingHomOnNeighborhood.Etale :=
  RingHom.Etale.respectsIso.1 C.componentCoordinateAlgHom.toRingHom
    C.componentNeighborhood.topIso.symm.commRingCatIsoToRingEquiv
      C.componentCoordinateAlgHom_etale

/-- Complex affine `n`-space is standard smooth of relative dimension `n`, using its presentation
with `n` variables and no relations. -/
lemma mvPolynomial_C_isStandardSmoothOfRelativeDimension :
    (MvPolynomial.C : ℂ →+* MvPolynomial (Fin n) ℂ).IsStandardSmoothOfRelativeDimension n := by
  rw [show (MvPolynomial.C : ℂ →+* MvPolynomial (Fin n) ℂ) =
    algebraMap ℂ (MvPolynomial (Fin n) ℂ) from rfl]
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  let P : Algebra.SubmersivePresentation ℂ (MvPolynomial (Fin n) ℂ)
      (Fin n) Empty :=
    { toPreSubmersivePresentation :=
        { toPresentation :=
            { toGenerators := Algebra.Generators.mvPolynomial ℂ (Fin n)
              relation := Empty.elim
              span_range_relation_eq_ker := by
                rw [Algebra.Generators.ker_mvPolynomial]
                simp }
          map := Empty.elim
          map_inj := fun a ↦ a.elim }
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
          Matrix.det_isEmpty]
        simpa only [map_one] using
          (isUnit_one : IsUnit (1 : MvPolynomial (Fin n) ℂ)) }
  exact P.isStandardSmoothOfRelativeDimension (by
    simp [Algebra.Presentation.dimension])

/-- The structure map of the exact affine component neighborhood is standard smooth of the
coordinate package's specified dimension on global sections. -/
lemma neighborhoodStructureMap_appTop_isStandardSmoothOfRelativeDimension :
    C.neighborhoodStructureMap.appTop.hom.IsStandardSmoothOfRelativeDimension n := by
  have hcoord0 : C.coordinateRingHomOnNeighborhood.IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.mp
      C.coordinateRingHomOnNeighborhood_etale
  have hcomposite :
      RingHom.IsStandardSmoothOfRelativeDimension n
        (C.coordinateRingHomOnNeighborhood.comp MvPolynomial.C) := by
    simpa only [zero_add] using
      hcoord0.comp (mvPolynomial_C_isStandardSmoothOfRelativeDimension (n := n))
  have hcat := C.C_comp_coordinateRingHomOnNeighborhood
  have hcomp :
      RingHom.IsStandardSmoothOfRelativeDimension n
        (C.neighborhoodStructureMap.appTop.hom.comp
          (Scheme.ΓSpecIso ↧ℂ).inv.hom) := by
    have hring := congrArg CommRingCat.Hom.hom hcat
    change C.coordinateRingHomOnNeighborhood.comp MvPolynomial.C =
      C.neighborhoodStructureMap.appTop.hom.comp
        (Scheme.ΓSpecIso ↧ℂ).inv.hom at hring
    rw [← hring]
    exact hcomposite
  have h := hcomp.comp
    (RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (Scheme.ΓSpecIso ↧ℂ).commRingCatIsoToRingEquiv)
  have heq :
      (C.neighborhoodStructureMap.appTop.hom.comp
        (Scheme.ΓSpecIso ↧ℂ).inv.hom).comp
          (Scheme.ΓSpecIso ↧ℂ).hom.hom =
        C.neighborhoodStructureMap.appTop.hom := by
    ext a
    have ha := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso ↧ℂ).hom_inv_id a
    exact congrArg C.neighborhoodStructureMap.appTop.hom ha
  rw [add_zero] at h
  exact heq ▸ h

/-- The exact coordinates prove that the selected affine component neighborhood is smooth of the
specified relative dimension. -/
noncomputable instance neighborhoodSmoothOfRelativeDimension :
    SmoothOfRelativeDimension n C.neighborhoodStructureMap where
  exists_isStandardSmoothOfRelativeDimension y := by
    let : IsAffine C.componentNeighborhood.toScheme :=
      C.componentNeighborhood_isAffine
    refine ⟨⊤, isAffineOpen_top _, C.neighborhoodStructureMap ⁻¹ᵁ ⊤,
      ?_, by simp, le_rfl, ?_⟩
    · simpa using (isAffineOpen_top C.componentNeighborhood.toScheme)
    · rw [Scheme.Hom.appLE_eq_app]
      exact C.neighborhoodStructureMap_appTop_isStandardSmoothOfRelativeDimension

noncomputable local instance coordinateRingAlgebra :
    Algebra (MvPolynomial (Fin n) ℂ) Γ(C.componentNeighborhood.toScheme, ⊤) :=
  C.coordinateRingHomOnNeighborhood.toAlgebra

noncomputable local instance coordinateRingComplexAlgebra :
    Algebra ℂ Γ(C.componentNeighborhood.toScheme, ⊤) :=
  (C.coordinateRingHomOnNeighborhood.comp MvPolynomial.C).toAlgebra

noncomputable local instance coordinateRingScalarTower :
    IsScalarTower ℂ (MvPolynomial (Fin n) ℂ)
      Γ(C.componentNeighborhood.toScheme, ⊤) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

noncomputable local instance coordinateRingEtale :
    Algebra.Etale (MvPolynomial (Fin n) ℂ)
      Γ(C.componentNeighborhood.toScheme, ⊤) :=
  RingHom.etale_algebraMap.mp C.coordinateRingHomOnNeighborhood_etale

/-- The affine neighborhood's canonical map to its spectrum respects the complex structure
induced by the exact component coordinates. -/
lemma neighborhoodToSpecΓ_over :
    C.componentNeighborhood.toScheme.toSpecΓ ≫
        ComplexPoint.affineSpecStructureMap Γ(C.componentNeighborhood.toScheme, ⊤) =
      C.neighborhoodStructureMap := by
  let φ : ↧ℂ ⟶ Γ(C.componentNeighborhood.toScheme, ⊤) :=
    CommRingCat.ofHom MvPolynomial.C ≫
      CommRingCat.ofHom C.coordinateRingHomOnNeighborhood
  change C.componentNeighborhood.toScheme.toSpecΓ ≫ Spec.map φ =
    C.neighborhoodStructureMap
  change (ΓSpec.adjunction.homEquiv C.componentNeighborhood.toScheme
    (Opposite.op ↧ℂ)) φ.op = C.neighborhoodStructureMap
  exact ext_to_Spec ((ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ).trans
    C.C_comp_coordinateRingHomOnNeighborhood)

/-- The canonical affine-spectrum isomorphism, bundled over `Spec ℂ`. -/
def neighborhoodToSpecΓIso : C.neighborhoodScheme ≅
    Over.mk (ComplexPoint.affineSpecStructureMap Γ(C.componentNeighborhood.toScheme, ⊤)) := by
  letI : IsAffine C.componentNeighborhood.toScheme :=
    C.componentNeighborhood_isAffine
  letI : IsIso C.componentNeighborhood.toScheme.toSpecΓ :=
    IsAffine.affine
  exact Over.isoMk (asIso C.componentNeighborhood.toScheme.toSpecΓ)
    C.neighborhoodToSpecΓ_over

/-- Complex points of the affine component neighborhood as complex algebra homomorphisms on its
coordinate ring. -/
def neighborhoodPointAlgHomHomeomorph :
    @Homeomorph
      (ComplexPoint C.neighborhoodScheme)
      (Γ(C.componentNeighborhood.toScheme, ⊤) →ₐ[ℂ] ℂ)
      Point.analyticTopology
      (ComplexPoint.affineAlgebraHomTopology Γ(C.componentNeighborhood.toScheme, ⊤)) :=
  (Point.isoMapHomeomorph C.neighborhoodToSpecΓIso).trans
    (ComplexPoint.affineSpecHomeomorph Γ(C.componentNeighborhood.toScheme, ⊤))

/-- The affine algebra-homomorphism coordinate of a neighborhood point evaluates global
regular sections in the usual way. -/
lemma neighborhoodPointAlgHomHomeomorph_apply
    (z : ComplexPoint C.neighborhoodScheme)
    (r : Γ(C.componentNeighborhood.toScheme, ⊤)) :
    C.neighborhoodPointAlgHomHomeomorph z r = Point.evaluate ⊤ r z := by
  rw [neighborhoodPointAlgHomHomeomorph, Homeomorph.trans_apply]
  change ComplexPoint.affineSpecEquiv Γ(C.componentNeighborhood.toScheme, ⊤)
      (Point.isoMapHomeomorph C.neighborhoodToSpecΓIso z) r = _
  rw [ComplexPoint.affineSpecEquiv_apply, Point.isoMapHomeomorph_apply,
    Point.evaluate_map]
  change Point.evaluate ⊤
      (C.componentNeighborhood.toScheme.toSpecΓ.appTop
        ((Scheme.ΓSpecIso (.of Γ(C.componentNeighborhood.toScheme, ⊤))).inv r)) z = _
  rw [Scheme.toSpecΓ_appTop]
  change Point.evaluate ⊤
      ((Scheme.ΓSpecIso (.of Γ(C.componentNeighborhood.toScheme, ⊤))).hom
        ((Scheme.ΓSpecIso (.of Γ(C.componentNeighborhood.toScheme, ⊤))).inv r)) z = _
  have h := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso (.of Γ(C.componentNeighborhood.toScheme, ⊤))).inv_hom_id) r
  exact congrArg (fun s ↦ Point.evaluate ⊤ s z) h

/-- The actual local analytic chart supplied by the exact étale component coordinates. -/
def neighborhoodProjectionChart :
    OpenPartialHomeomorph
      (ComplexPoint C.neighborhoodScheme)
      (Fin n → ℂ) :=
  C.neighborhoodPointAlgHomHomeomorph.toOpenPartialHomeomorph |>.trans
    (ComplexAlgHom.etaleAlgHomProjectionChart
      Γ(C.componentNeighborhood.toScheme, ⊤)
      (C.neighborhoodPointAlgHomHomeomorph C.neighborhoodPoint))

/-- The selected smooth point belongs to the source of the exact analytic component chart. -/
lemma neighborhoodPoint_mem_projectionChart_source :
    C.neighborhoodPoint ∈ C.neighborhoodProjectionChart.source := by
  rw [neighborhoodProjectionChart, OpenPartialHomeomorph.trans_source]
  exact ⟨by simp, ComplexAlgHom.mem_etaleAlgHomProjectionChart_source
    Γ(C.componentNeighborhood.toScheme, ⊤)
      (C.neighborhoodPointAlgHomHomeomorph C.neighborhoodPoint)⟩

/-- On its source, the component chart is exactly restriction of a complex point along the
retained polynomial coordinate map, followed by evaluation on the coordinate variables. -/
lemma neighborhoodProjectionChart_apply_of_mem
    (z : ComplexPoint C.neighborhoodScheme)
    (hz : z ∈ C.neighborhoodProjectionChart.source) :
    C.neighborhoodProjectionChart z =
      ComplexAlgHom.mvPolynomialAlgHomHomeomorph n
        (ComplexAlgHom.etaleBaseAlgHom Γ(C.componentNeighborhood.toScheme, ⊤)
          (C.neighborhoodPointAlgHomHomeomorph z)) := by
  rw [neighborhoodProjectionChart, OpenPartialHomeomorph.trans_source] at hz
  rw [neighborhoodProjectionChart, OpenPartialHomeomorph.trans_apply]
  exact ComplexAlgHom.etaleAlgHomProjectionChart_apply_of_mem (n := n)
    Γ(C.componentNeighborhood.toScheme, ⊤)
      (C.neighborhoodPointAlgHomHomeomorph C.neighborhoodPoint)
      (C.neighborhoodPointAlgHomHomeomorph z) hz.2

/-- Evaluation of a global section of the affine component neighborhood is analytic along the
inverse of its exact projection chart. -/
lemma analyticAt_neighborhoodProjectionChart_symm_evaluate_top
    {w : Fin n → ℂ} (hw : w ∈ C.neighborhoodProjectionChart.target)
    (r : Γ(C.componentNeighborhood.toScheme, ⊤)) :
    AnalyticAt ℂ (fun v ↦ Point.evaluate ⊤ r
      (C.neighborhoodProjectionChart.symm v)) w := by
  let u := C.neighborhoodPointAlgHomHomeomorph C.neighborhoodPoint
  have hw' : w ∈ (ComplexAlgHom.etaleAlgHomProjectionChart
      Γ(C.componentNeighborhood.toScheme, ⊤) u).target := by
    rw [neighborhoodProjectionChart, OpenPartialHomeomorph.trans_target] at hw
    exact hw.1
  have h := ComplexAlgHom.analyticAt_etaleAlgHomProjectionChart_symm_apply
    Γ(C.componentNeighborhood.toScheme, ⊤) u hw' r
  have h' : AnalyticAt ℂ (fun v ↦ C.neighborhoodPointAlgHomHomeomorph
      (C.neighborhoodProjectionChart.symm v) r) w := by
    apply h.congr
    filter_upwards with v
    simp only [neighborhoodProjectionChart, OpenPartialHomeomorph.coe_trans_symm,
      Function.comp_apply, Homeomorph.toOpenPartialHomeomorph_symm_apply]
    rw [Homeomorph.apply_symm_apply]
  simpa only [C.neighborhoodPointAlgHomHomeomorph_apply] using h'

/-- Evaluation of an arbitrary regular section defined near the inverse-chart point is analytic
there.  The proof shrinks inside the affine neighborhood to a principal open and represents the
section by a quotient of global sections. -/
lemma analyticAt_neighborhoodProjectionChart_symm_evaluate
    {w : Fin n → ℂ} (hw : w ∈ C.neighborhoodProjectionChart.target)
    (W : C.componentNeighborhood.toScheme.Opens) (s : Γ(C.componentNeighborhood.toScheme, W))
    (hW : C.neighborhoodProjectionChart.symm w ∈ Point.overOpen W) :
    AnalyticAt ℂ (fun v ↦ Point.evaluate W s
      (C.neighborhoodProjectionChart.symm v)) w := by
  let Y := C.neighborhoodScheme
  let : IsAffine Y.left := C.componentNeighborhood_isAffine
  let y : ComplexPoint Y := C.neighborhoodProjectionChart.symm w
  obtain ⟨g, hgW, hyg⟩ :=
    (isAffineOpen_top Y.left).exists_basicOpen_le
      (V := W) ⟨y.underlying, hW⟩ trivial
  let t : Γ(Y.left, Y.left.basicOpen g) := Y.left.presheaf.map (homOfLE hgW).op s
  obtain ⟨k, a, hquot⟩ :=
    ComplexPoint.exists_evaluate_affine_basicOpen_eq_div (X := Y) g t
  have hyg' : y ∈ Point.overOpen (Y.left.basicOpen g) := hyg
  have hgzero : Point.evaluate ⊤ g y ≠ 0 :=
    (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero g y trivial).mp hyg'
  have ha := C.analyticAt_neighborhoodProjectionChart_symm_evaluate_top hw a
  have hg := C.analyticAt_neighborhoodProjectionChart_symm_evaluate_top hw g
  have hrat : AnalyticAt ℂ
      (fun v ↦ Point.evaluate ⊤ a (C.neighborhoodProjectionChart.symm v) /
        Point.evaluate ⊤ g (C.neighborhoodProjectionChart.symm v) ^ k) w :=
    ha.div (hg.pow k) (pow_ne_zero k hgzero)
  apply hrat.congr
  have hcontinuous : ContinuousAt C.neighborhoodProjectionChart.symm w :=
    C.neighborhoodProjectionChart.continuousAt_symm hw
  have heventually : C.neighborhoodProjectionChart.symm ⁻¹'
      Point.overOpen (Y.left.basicOpen g) ∈ 𝓝 w :=
    hcontinuous ((Point.isOpen_overOpen (Y.left.basicOpen g)).mem_nhds hyg')
  filter_upwards [heventually] with v hv
  let yv : ComplexPoint Y :=
    C.neighborhoodProjectionChart.symm v
  have hres := Point.evaluate_res hgW s yv hv
  exact (hres.trans (hquot yv hv)).symm

/-- The relative-homology map induced by the actual analytic chart coming from the exact
component coordinates. -/
def neighborhoodLocalHomologyMap :
    AlgebraicTopology.Singular.RelativeHomology ℚ
        (AlgebraicTopology.Singular.standardComplexPuncturedPair n) (2 * n) →ₗ[ℚ]
      AlgebraicTopology.Singular.RelativeHomology ℚ
        (AlgebraicTopology.Singular.pointComplementPair C.neighborhoodPoint) (2 * n) :=
  AlgebraicTopology.Singular.relativeHomologyMap ℚ (2 * n)
    (AlgebraicTopology.Singular.chartModelEmbeddingPair n
      C.neighborhoodProjectionChart C.neighborhoodPoint
        C.neighborhoodPoint_mem_projectionChart_source)

/-- The standard complex local class transported through the exact analytic component chart. -/
def neighborhoodLocalClass :
    AlgebraicTopology.Singular.RelativeHomology ℚ
      (AlgebraicTopology.Singular.pointComplementPair C.neighborhoodPoint) (2 * n) :=
  C.neighborhoodLocalHomologyMap
    (AlgebraicTopology.Singular.standardComplexLocalClass n)

/-- The transported class is the chart-local class defined by the general chart construction. -/
lemma neighborhoodLocalClass_eq_localClassOfChart :
    C.neighborhoodLocalClass =
      AlgebraicTopology.Singular.localClassOfChart n C.neighborhoodProjectionChart
        C.neighborhoodPoint C.neighborhoodPoint_mem_projectionChart_source :=
  rfl

end CycleComponentSeparateLocalCoordinates
end AlgebraicGeometry

namespace AlgebraicTopology.Singular

/-- The oriented standard complex local class generates rational local homology in every complex
dimension. -/
lemma span_standardComplexLocalClass_eq_top (n : ℕ) :
    Submodule.span ℚ {standardComplexLocalClass n} = ⊤ := by
  cases n with
  | zero => exact span_standardComplexLocalClass_zero_eq_top
  | succ n =>
      rw [span_standardComplexLocalClass_eq_top_iff]
      have hdeg : (n + 1) * 2 = n * 2 + 2 := by lia
      rw [hdeg]
      exact span_standardLocalClass_add_two_eq_top (n * 2)

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.CycleComponentSeparateLocalCoordinates

noncomputable local instance {Y : Over (Spec ↧ℂ)} :
    TopologicalSpace (ComplexPoint Y) := Point.analyticTopology

variable {d n : ℕ} {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom] {x : X.left}
  [SmoothOfRelativeDimension d X.hom]
  (C : CycleComponentSeparateLocalCoordinates X x d n)

/-- The transported local class generates exactly the image of the chart-induced local-homology
map. This is the algebraic intermediate identity used by the full generator theorem below. -/
lemma span_neighborhoodLocalClass_eq_range :
    Submodule.span ℚ {C.neighborhoodLocalClass} =
      LinearMap.range C.neighborhoodLocalHomologyMap := by
  calc
    Submodule.span ℚ {C.neighborhoodLocalClass} =
        (Submodule.span ℚ
          {AlgebraicTopology.Singular.standardComplexLocalClass n}).map
            C.neighborhoodLocalHomologyMap := by
      rw [Submodule.map_span]
      simp only [Set.image_singleton, neighborhoodLocalClass]
    _ = (⊤ : Submodule ℚ _).map C.neighborhoodLocalHomologyMap := by
      rw [AlgebraicTopology.Singular.span_standardComplexLocalClass_eq_top]
    _ = LinearMap.range C.neighborhoodLocalHomologyMap :=
      Submodule.map_top C.neighborhoodLocalHomologyMap

/-- The transported class generates the full local homology of the affine component
neighborhood.  The missing surjectivity in `span_neighborhoodLocalClass_eq_range` is supplied by
open-neighborhood excision for the target of the compressed chart. -/
lemma span_neighborhoodLocalClass_eq_top :
    Submodule.span ℚ {C.neighborhoodLocalClass} = ⊤ := by
  let : IsAffine C.neighborhoodScheme.left :=
    C.componentNeighborhood_isAffine
  let : T2Space
      (ComplexPoint C.neighborhoodScheme) :=
    ComplexPoint.t2Space_of_isAffine C.neighborhoodScheme
  rw [C.neighborhoodLocalClass_eq_localClassOfChart]
  exact AlgebraicTopology.Singular.span_localClassOfChart_eq_top
    n C.neighborhoodProjectionChart C.neighborhoodPoint
      C.neighborhoodPoint_mem_projectionChart_source

/-- In ambient dimension at most two, the established exact component coordinates provide an
actual analytic chart whose transported class generates the chart map's image. -/
lemma exists_span_neighborhoodLocalClass_eq_range_of_le_two
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (d p : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (hx : Order.coheight x = p) (hd : d ≤ 2) :
    ∃ C : CycleComponentSeparateLocalCoordinates X x d (d - p),
      Submodule.span ℚ {C.neighborhoodLocalClass} =
        LinearMap.range C.neighborhoodLocalHomologyMap := by
  obtain ⟨C⟩ := nonempty_cycleComponentSeparateLocalCoordinates_of_le_two
    X x d p hx hd
  exact ⟨C, C.span_neighborhoodLocalClass_eq_range⟩

/-- In ambient dimension at most two, exact component coordinates give an actual generator of
the full local homology at the selected smooth component point. -/
lemma exists_span_neighborhoodLocalClass_eq_top_of_le_two
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (d p : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (hx : Order.coheight x = p) (hd : d ≤ 2) :
    ∃ C : CycleComponentSeparateLocalCoordinates X x d (d - p),
      Submodule.span ℚ {C.neighborhoodLocalClass} = ⊤ := by
  obtain ⟨C⟩ := nonempty_cycleComponentSeparateLocalCoordinates_of_le_two
    X x d p hx hd
  exact ⟨C, C.span_neighborhoodLocalClass_eq_top⟩

/-- A codimension-`d` component has an exact zero-dimensional component chart whose transported
class generates the chart map's image. -/
lemma exists_span_neighborhoodLocalClass_eq_range_of_coheight_eq_dimension
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (hx : Order.coheight x = d) :
    ∃ C : CycleComponentSeparateLocalCoordinates X x d 0,
      Submodule.span ℚ {C.neighborhoodLocalClass} =
        LinearMap.range C.neighborhoodLocalHomologyMap := by
  obtain ⟨C⟩ :=
    nonempty_cycleComponentSeparateLocalCoordinates_of_coheight_eq_dimension
      X x d hx
  exact ⟨C, C.span_neighborhoodLocalClass_eq_range⟩

/-- A codimension-`d` component has an actual generator of its zero-dimensional local homology
at the selected smooth point. -/
lemma exists_span_neighborhoodLocalClass_eq_top_of_coheight_eq_dimension
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (hx : Order.coheight x = d) :
    ∃ C : CycleComponentSeparateLocalCoordinates X x d 0,
      Submodule.span ℚ {C.neighborhoodLocalClass} = ⊤ := by
  obtain ⟨C⟩ :=
    nonempty_cycleComponentSeparateLocalCoordinates_of_coheight_eq_dimension
      X x d hx
  exact ⟨C, C.span_neighborhoodLocalClass_eq_top⟩

/-- A one-dimensional component has an exact one-dimensional component chart whose transported
class generates the chart map's image. -/
lemma exists_span_neighborhoodLocalClass_eq_range_of_coheight_succ_eq_dimension
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (d p : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (hx : Order.coheight x = p) (hd : p + 1 = d) :
    ∃ C : CycleComponentSeparateLocalCoordinates X x d 1,
      Submodule.span ℚ {C.neighborhoodLocalClass} =
        LinearMap.range C.neighborhoodLocalHomologyMap := by
  obtain ⟨C⟩ :=
    nonempty_cycleComponentSeparateLocalCoordinates_of_coheight_succ_eq_dimension
      X x d p hx hd
  exact ⟨C, C.span_neighborhoodLocalClass_eq_range⟩

/-- A one-dimensional component has an actual generator of its local homology at the selected
smooth point. -/
lemma exists_span_neighborhoodLocalClass_eq_top_of_coheight_succ_eq_dimension
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (d p : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (hx : Order.coheight x = p) (hd : p + 1 = d) :
    ∃ C : CycleComponentSeparateLocalCoordinates X x d 1,
      Submodule.span ℚ {C.neighborhoodLocalClass} = ⊤ := by
  obtain ⟨C⟩ :=
    nonempty_cycleComponentSeparateLocalCoordinates_of_coheight_succ_eq_dimension
      X x d p hx hd
  exact ⟨C, C.span_neighborhoodLocalClass_eq_top⟩

end AlgebraicGeometry.CycleComponentSeparateLocalCoordinates
