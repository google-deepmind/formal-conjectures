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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ComplexLocalOrientationNeighborhood
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.HomologySheafSection
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SheafMapOfLocallyRepresentableStalks
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularChainSheafOrientation

/-!
# The normalized complex orientation of the singular homology sheaf

The complex local classes are represented by relative homology classes on open
neighborhoods, and the canonical relative-homology-to-sheaf-section map makes them locally
representable in the homology sheaf. Unique sheaf gluing constructs the map from the
constant rational sheaf, and the normalized local generator theorem shows it is an
isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ))) (d : ℕ)

noncomputable local instance complexOrientationHomologySheafAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

variable [SmoothOfRelativeDimension d X.hom]
  [T2Space (ComplexPoint X)]

/-- Scalar multiples of the exact normalized local orientation, viewed in the actual
homology-sheaf stalk through its canonical local-homology comparison. -/
def complexOrientationHomologyStalkMap (x : ComplexPoint X) :
    AddCommGrpCat.of ℚ ⟶
      (singularChainHomologySheaf ℚ (TopCat.of (ComplexPoint X)) (2 * d)).presheaf.stalk x :=
  AddCommGrpCat.ofHom
    ((LinearMap.toSpanSingleton ℚ _ (complexLocalOrientation X d x)).toAddMonoidHom) ≫
      (singularChainHomologySheafStalkIso ℚ (TopCat.of (ComplexPoint X)) x (2 * d)).inv

/-- Local representability is proved using the actual geometric neighborhood class,
not assumed as an orientation-sheaf field. -/
theorem complexOrientationHomologyStalkMap_locallyRepresentable :
    ∀ (q : ℚ) (x : ComplexPoint X),
      ∃ (U : Opens (ComplexPoint X)) (_ : x ∈ U)
        (s : (singularChainHomologySheaf ℚ (TopCat.of (ComplexPoint X))
          (2 * d)).presheaf.obj (op U)),
        ∀ (y : ComplexPoint X) (hy : y ∈ U),
          (singularChainHomologySheaf ℚ (TopCat.of (ComplexPoint X))
            (2 * d)).presheaf.germ U y hy s =
              complexOrientationHomologyStalkMap X d y q := by
  intro q x
  let U := complexLocalOrientationNeighborhood X d x
  let c := complexLocalOrientationNeighborhoodClass X d x
  refine ⟨U, mem_complexLocalOrientationNeighborhood X d x,
    relativeHomologyToHomologySheafSection ℚ (TopCat.of (ComplexPoint X))
      U (2 * d) (q • c), ?_⟩
  intro y hy
  apply ((ConcreteCategory.isIso_iff_bijective
    (singularChainHomologySheafStalkIso ℚ (TopCat.of (ComplexPoint X))
      y (2 * d)).hom).mp inferInstance).injective
  have hgerm := ConcreteCategory.congr_hom
    (relativeHomologyToHomologySheafSection_germ ℚ
      (TopCat.of (ComplexPoint X)) U y hy (2 * d)) (q • c)
  simp only [ConcreteCategory.comp_apply] at hgerm
  erw [hgerm]
  change relativeHomologyMap ℚ (2 * d) (supportInclusionPairMap _ _) (q • c) =
    (singularChainHomologySheafStalkIso ℚ (TopCat.of (ComplexPoint X))
      y (2 * d)).hom ((singularChainHomologySheafStalkIso ℚ
        (TopCat.of (ComplexPoint X)) y (2 * d)).inv
          (q • complexLocalOrientation X d y))
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id]
  change relativeHomologyMap ℚ (2 * d) (supportInclusionPairMap _ _) (q • c) =
    q • complexLocalOrientation X d y
  rw [map_smul]
  exact congrArg (q • ·) (complexLocalOrientationNeighborhoodClass_restrict X d x y hy)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Each stalk map is an isomorphism by the already constructed, exactly normalized
local generator theorem. -/
theorem complexOrientationHomologyStalkMap_isIso (x : ComplexPoint X) :
    IsIso (complexOrientationHomologyStalkMap X d x) := by
  have hne : complexLocalOrientation X d x ≠ 0 :=
    localClassOfChart_ne_zero d (localChart X d x) x
      (mem_localChart_source X d x)
  have hbij : Function.Bijective (LinearMap.toSpanSingleton ℚ _
      (complexLocalOrientation X d x)) := by
    refine ⟨smul_left_injective ℚ hne, fun a ↦ Submodule.mem_span_singleton.mp ?_⟩
    rw [span_complexLocalOrientation_eq_top]
    exact Submodule.mem_top
  let : IsIso (AddCommGrpCat.ofHom
      ((LinearMap.toSpanSingleton ℚ _ (complexLocalOrientation X d x)).toAddMonoidHom)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  unfold complexOrientationHomologyStalkMap
  infer_instance

/-- The actual sheaf map obtained by gluing the geometric neighborhood orientations. -/
def constantToComplexOrientationHomologySheaf :
    singularOrientationConstantSheaf ℚ (TopCat.of (ComplexPoint X)) ⟶
      singularChainHomologySheaf ℚ (TopCat.of (ComplexPoint X)) (2 * d) :=
  TopCat.Sheaf.constantSheafMapOfLocallyRepresentable _ (AddCommGrpCat.of ℚ)
    (complexOrientationHomologyStalkMap X d)
    (complexOrientationHomologyStalkMap_locallyRepresentable X d)

/-- The constructed normalized orientation is an isomorphism of actual sheaves. -/
def complexOrientationHomologySheafIso :
    singularOrientationConstantSheaf ℚ (TopCat.of (ComplexPoint X)) ≅
      singularChainHomologySheaf ℚ (TopCat.of (ComplexPoint X)) (2 * d) := by
  letI : IsIso (constantToComplexOrientationHomologySheaf X d) := by
    unfold constantToComplexOrientationHomologySheaf
    exact TopCat.Sheaf.constantSheafMapOfLocallyRepresentable_isIso
      (singularChainHomologySheaf ℚ (TopCat.of (ComplexPoint X)) (2 * d))
      (AddCommGrpCat.of ℚ)
      (complexOrientationHomologyStalkMap X d)
      (complexOrientationHomologyStalkMap_locallyRepresentable X d)
      (complexOrientationHomologyStalkMap_isIso X d)
  exact asIso (constantToComplexOrientationHomologySheaf X d)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- On every stalk the assembled sheaf isomorphism is scalar multiplication by the
exact complex orientation, through the canonical constant and local-homology maps. -/
@[reassoc]
theorem complexOrientationHomologySheafIso_stalk (x : ComplexPoint X) :
    (TopCat.Sheaf.constantSheafStalkIso (X := TopCat.of (ComplexPoint X))
      (AddCommGrpCat.of ℚ) x).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (complexOrientationHomologySheafIso X d).hom.hom ≫
      (singularChainHomologySheafStalkIso ℚ (TopCat.of (ComplexPoint X))
        x (2 * d)).hom =
      AddCommGrpCat.ofHom
        ((LinearMap.toSpanSingleton ℚ _ (complexLocalOrientation X d x)).toAddMonoidHom) := by
  change _ ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    (constantToComplexOrientationHomologySheaf X d).hom ≫ _ = _
  unfold constantToComplexOrientationHomologySheaf
  rw [← Category.assoc]
  erw [TopCat.Sheaf.constantSheafMapOfLocallyRepresentable_stalk]
  unfold complexOrientationHomologyStalkMap
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- In particular the isomorphism sends the germ of the constant section `1` to
the exact normalized complex local fundamental class. -/
theorem complexOrientationHomologySheafIso_stalk_one (x : ComplexPoint X) :
    ((TopCat.Sheaf.constantSheafStalkIso (X := TopCat.of (ComplexPoint X))
      (AddCommGrpCat.of ℚ) x).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (complexOrientationHomologySheafIso X d).hom.hom ≫
      (singularChainHomologySheafStalkIso ℚ (TopCat.of (ComplexPoint X))
        x (2 * d)).hom) 1 = complexLocalOrientation X d x := by
  rw [complexOrientationHomologySheafIso_stalk]
  exact LinearMap.toSpanSingleton_apply_one ℚ _ (complexLocalOrientation X d x)

end AlgebraicGeometry.ComplexPoint
