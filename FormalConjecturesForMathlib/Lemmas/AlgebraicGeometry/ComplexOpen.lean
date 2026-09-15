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
# Complex points of open subschemes

Analytification respects restriction to an open subscheme. More precisely, complex points of an
open subscheme are canonically homeomorphic to the corresponding open subspace of the complex
points of the ambient scheme. In particular, an open immersion of this form induces an open
embedding on complex points.
-/

@[expose] public section

open CategoryTheory Topology

namespace AlgebraicGeometry.ComplexPoint

open Point

noncomputable section

noncomputable local instance {Y : Over (Spec ↧ℂ)} :
    TopologicalSpace (ComplexPoint Y) := analyticTopology

variable (X : Over (Spec ↧ℂ)) (U : X.left.Opens)

/-- An open subscheme with its induced complex structure. -/
abbrev openScheme : Over (Spec ↧ℂ) :=
  Over.mk (U.ι ≫ X.hom)

/-- The inclusion of an open subscheme as a morphism over `Spec ℂ`. -/
abbrev openInclusion :
    openScheme X U ⟶ X :=
  Over.homMk U.ι rfl

/-- The image of a complex point lying in `U` is contained in the image of its inclusion. -/
lemma point_range_subset (z : ComplexPoint X) (hz : z ∈ overOpen U) :
    Set.range z.left ⊆ Set.range U.ι := by
  rintro y ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  have hx : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := Spec ↧ℂ) _ _
  subst x
  exact hz

/-- A complex point in an open set factors through the corresponding open subscheme. -/
def liftToOpen (z : ComplexPoint X) (hz : z ∈ overOpen U) :
    Spec ↧ℂ ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι z.left (point_range_subset X U z hz)

@[reassoc (attr := simp)]
lemma liftToOpen_fac (z : ComplexPoint X) (hz : z ∈ overOpen U) :
    liftToOpen X U z hz ≫ U.ι = z.left :=
  IsOpenImmersion.lift_fac _ _ _

/-- A point of `X` lying in `U`, regarded as a complex point of the open subscheme `U`. -/
def asOpenPoint (z : ComplexPoint X) (hz : z ∈ overOpen U) :
    ComplexPoint (openScheme X U) :=
  Over.homMk (liftToOpen X U z hz) (by
    change liftToOpen X U z hz ≫ (U.ι ≫ X.hom) = 𝟙 _
    rw [← Category.assoc, liftToOpen_fac]
    exact Over.w z)

/-- Complex points of an open subscheme are the ambient complex points lying in the open. -/
def openEquiv :
    ComplexPoint (openScheme X U) ≃
      {z : ComplexPoint X // z ∈ overOpen U} where
  toFun z := ⟨map (openInclusion X U) z, by
    change (map (openInclusion X U) z).underlying ∈ U
    rw [underlying_map]
    exact z.underlying.property⟩
  invFun z := asOpenPoint X U z.1 z.2
  left_inv z := by
    apply Over.OverMorphism.ext
    symm
    apply IsOpenImmersion.lift_uniq U.ι (map (openInclusion X U) z).left
    simp [map]
  right_inv z := Subtype.ext (Over.OverMorphism.ext (liftToOpen_fac X U z.1 z.2))

@[simp]
lemma openEquiv_coe (z : ComplexPoint (openScheme X U)) :
    (openEquiv X U z).1 = map (openInclusion X U) z :=
  rfl

/-- The map from an open subscheme to its ambient open subspace is continuous. -/
lemma continuous_openEquiv :
    @Continuous
      (ComplexPoint (openScheme X U))
      {z : ComplexPoint X // z ∈ overOpen U}
      analyticTopology (TopologicalSpace.induced Subtype.val analyticTopology)
      (openEquiv X U) :=
  @Continuous.subtype_mk
    (ComplexPoint X)
    (ComplexPoint (openScheme X U))
    analyticTopology analyticTopology
    (fun z ↦ z ∈ overOpen U) (map (openInclusion X U))
    (continuous_map (openInclusion X U)) _

/-- Evaluation is unchanged when both a point and a section are transported across equal opens. -/
lemma evaluate_eq {Y : Over (Spec ↧ℂ)}
    {V W : Y.left.Opens} (e : V = W) (t : Γ(Y.left, V)) (z : ComplexPoint Y) :
    evaluate V t z = evaluate W (Y.left.presheaf.map (eqToHom e.symm).op t) z := by
  subst e
  simp

/-- Evaluation commutes with the equivalence between an open subscheme and its ambient open. -/
lemma evaluate_openEquiv {V : U.toScheme.Opens} (t : Γ(U.toScheme, V))
    (z : ComplexPoint (openScheme X U)) :
    evaluate (U.ι ''ᵁ V) ((U.ι.appIso V).inv t) (map (openInclusion X U) z) =
      evaluate V t z := by
  rw [evaluate_map]
  let e : U.ι ⁻¹ᵁ U.ι ''ᵁ V = V := U.ι.preimage_image_eq V
  let q := U.ι.app (U.ι ''ᵁ V) ((U.ι.appIso V).inv t)
  have hq : q = U.toScheme.presheaf.map (eqToHom e).op t := by
    change ((U.ι.appIso V).inv ≫ U.ι.app (U.ι ''ᵁ V)) t = _
    rw [U.ι.appIso_inv_app]
  calc
    evaluate (U.ι ⁻¹ᵁ U.ι ''ᵁ V) q z =
        evaluate V (U.toScheme.presheaf.map (eqToHom e.symm).op q) z :=
      evaluate_eq (Y := openScheme X U) e q z
    _ = evaluate V t z := by
      congr 2
      rw [hq]
      change (U.toScheme.presheaf.map (eqToHom e).op ≫
        U.toScheme.presheaf.map (eqToHom e.symm).op) t = t
      rw [← Functor.map_comp]
      simp
      rfl

/-- The inverse map from the ambient open subspace is continuous. -/
lemma continuous_openEquiv_symm :
    @Continuous
      {z : ComplexPoint X // z ∈ overOpen U}
      (ComplexPoint (openScheme X U))
      (TopologicalSpace.induced Subtype.val analyticTopology) analyticTopology
      (openEquiv X U).symm := by
  rw [continuous_iff_analyticSubbasis]
  rintro W ⟨V, t, O, hO, rfl⟩
  let A : Set (ComplexPoint X) := overOpen (U.ι ''ᵁ V) ∩
    evaluate (U.ι ''ᵁ V) ((U.ι.appIso V).inv t) ⁻¹' O
  have hA : @IsOpen (ComplexPoint X) analyticTopology A :=
    isOpen_overOpen_inter_preimage _ _ _ hO
  rw [show (openEquiv X U).symm ⁻¹'
      (overOpen V ∩ evaluate V t ⁻¹' O) = Subtype.val ⁻¹' A by
    ext y
    let z := (openEquiv X U).symm y
    have hy : openEquiv X U z = y :=
      (openEquiv X U).apply_symm_apply y
    rw [← hy]
    simp only [Set.mem_preimage, Equiv.symm_apply_apply, Set.mem_inter_iff]
    change (z ∈ overOpen V ∧ evaluate V t z ∈ O) ↔
      (map (openInclusion X U) z ∈ overOpen (U.ι ''ᵁ V) ∧
        evaluate (U.ι ''ᵁ V) ((U.ι.appIso V).inv t) (map (openInclusion X U) z) ∈ O)
    rw [evaluate_openEquiv]
    exact and_congr_left' (by simp [overOpen])]
  exact @isOpen_induced
    {z : ComplexPoint X // z ∈ overOpen U}
    (ComplexPoint X) analyticTopology Subtype.val A hA

/-- Analytification of an open subscheme is the corresponding analytic open subspace. -/
def openHomeomorph :
    @Homeomorph
      (ComplexPoint (openScheme X U))
      {z : ComplexPoint X // z ∈ overOpen U}
      analyticTopology (TopologicalSpace.induced Subtype.val analyticTopology) where
  toEquiv := openEquiv X U
  continuous_toFun := continuous_openEquiv X U
  continuous_invFun := continuous_openEquiv_symm X U

/-- Inclusion of an open subscheme induces an open embedding on complex points. -/
lemma isOpenEmbedding_map_open :
    IsOpenEmbedding (map (openInclusion X U) :
      ComplexPoint (openScheme X U) → ComplexPoint X) := by
  have hU : IsOpen (overOpen U : Set (ComplexPoint X)) := isOpen_overOpen (X := X) U
  have h := hU.isOpenEmbedding_subtypeVal.comp (openHomeomorph X U).isOpenEmbedding
  simpa [Function.comp_def, openHomeomorph, openEquiv] using h

end


end AlgebraicGeometry.ComplexPoint
