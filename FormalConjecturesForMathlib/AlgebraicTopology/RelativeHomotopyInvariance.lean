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

public import FormalConjecturesForMathlib.AlgebraicTopology.SingularCohomology
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-!
# Homotopy invariance of relative singular homology

The relative singular chain complex in `SingularCohomology` is the cokernel of the
inclusion of singular chains on the subspace. This file shows that a homotopy of maps of
topological pairs descends from the usual singular prism operator to this cokernel. Consequently,
homotopic maps of pairs induce the same map on relative singular homology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open AlgebraicTopology.Singular MonoidalCategory
open scoped Simplicial

universe u v w

namespace TopCat.Homotopy

variable {X X' Y Y' : TopCat.{u}}
variable {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}

/-- The simplicial prism associated to a topological homotopy is natural with respect to a
commuting square of homotopies. -/
lemma toSimplicialObjectHomotopy_h_naturality
    (H : TopCat.Homotopy f g) (H' : TopCat.Homotopy f' g')
    (a : X' ⟶ X) (b : Y' ⟶ Y)
    (hw : a ▷ I ≫ H.h = H'.h ≫ b) {n : ℕ} (i : Fin (n + 1)) :
    (H.toSSet.toSimplicialObjectHomotopy.precomp (TopCat.toSSet.map a)).h i =
      (H'.toSSet.toSimplicialObjectHomotopy.postcomp (TopCat.toSSet.map b)).h i := by
  ext x
  simp only [CategoryTheory.SimplicialObject.Homotopy.precomp_h,
    CategoryTheory.SimplicialObject.Homotopy.postcomp_h]
  dsimp [SSet.Homotopy.toSimplicialObjectHomotopy, TopCat.Homotopy.toSSet]
  rw [← SSet.yonedaEquiv_symm_comp]
  have hmap :
      (SSet.yonedaEquiv.symm x ≫ TopCat.toSSet.map a) ▷ Δ[1] ≫
          (TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI) ≫
            Functor.LaxMonoidal.μ TopCat.toSSet X I ≫ TopCat.toSSet.map H.h =
        SSet.yonedaEquiv.symm x ▷ Δ[1] ≫
          (TopCat.toSSet.obj X' ◁ SSet.stdSimplex.toSSetObjI) ≫
            Functor.LaxMonoidal.μ TopCat.toSSet X' I ≫
              TopCat.toSSet.map H'.h ≫ TopCat.toSSet.map b := by
    simp only [MonoidalCategory.comp_whiskerRight, Category.assoc,
      ← MonoidalCategory.whisker_exchange_assoc,
      Functor.LaxMonoidal.μ_natural_left_assoc, ← Functor.map_comp, hw]
  exact ConcreteCategory.congr_hom (congr_app hmap _) _

end TopCat.Homotopy

namespace CategoryTheory.SimplicialObject.Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X X' Y Y' : SimplicialObject C}
variable {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}

/-- The chain homotopy obtained from a simplicial homotopy is natural componentwise. -/
lemma chainHomotopy_hom_naturality
    (H : Homotopy f g) (H' : Homotopy f' g')
    (a : X' ⟶ X) (b : Y' ⟶ Y)
    (hw : ∀ {n : ℕ} (i : Fin (n + 1)),
      a.app _ ≫ H.h i = H'.h i ≫ b.app _)
    (i j : ℕ) :
    ((alternatingFaceMapComplex C).map a).f i ≫ H.toChainHomotopy.hom i j =
      H'.toChainHomotopy.hom i j ≫
        ((alternatingFaceMapComplex C).map b).f j := by
  dsimp [toChainHomotopy, ToChainHomotopy.hom]
  split_ifs with hij
  · subst j
    simp only [eqToHom_refl, Category.comp_id]
    simp only [Preadditive.comp_neg, Preadditive.neg_comp,
      Preadditive.comp_sum, Preadditive.sum_comp,
      Preadditive.comp_zsmul, Preadditive.zsmul_comp]
    congr 2
    funext k
    rw [hw k]
  · simp

end CategoryTheory.SimplicialObject.Homotopy

namespace TopCat.Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts C]
variable {X X' Y Y' : TopCat.{w}}
variable {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}

/-- The usual singular chain homotopy is natural with respect to a commuting square of
topological homotopies. -/
lemma singularChainHomotopy_hom_naturality
    (H : TopCat.Homotopy f g) (H' : TopCat.Homotopy f' g')
    (a : X' ⟶ X) (b : Y' ⟶ Y)
    (hw : a ▷ I ≫ H.h = H'.h ≫ b) (R : C) (i j : ℕ) :
    (((singularChainComplexFunctor C).obj R).map a).f i ≫
        (H.singularChainComplexFunctorObjMap R).hom i j =
      (H'.singularChainComplexFunctorObjMap R).hom i j ≫
        (((singularChainComplexFunctor C).obj R).map b).f j := by
  apply CategoryTheory.SimplicialObject.Homotopy.chainHomotopy_hom_naturality
  intro n k
  change (sigmaConst.obj R).map ((TopCat.toSSet.map a).app _) ≫
      (sigmaConst.obj R).map (H.toSSet.toSimplicialObjectHomotopy.h k) =
    (sigmaConst.obj R).map (H'.toSSet.toSimplicialObjectHomotopy.h k) ≫
      (sigmaConst.obj R).map ((TopCat.toSSet.map b).app _)
  simpa only [CategoryTheory.SimplicialObject.Homotopy.precomp_h,
      CategoryTheory.SimplicialObject.Homotopy.postcomp_h, Functor.map_comp] using
    congrArg (fun z ↦ (sigmaConst.obj R).map z)
      (toSimplicialObjectHomotopy_h_naturality H H' a b hw k)

end TopCat.Homotopy

namespace TopPair.Homotopy

variable {R : Type u} [Field R]
variable {X Y : TopPair.{u}} {f g : X ⟶ Y}

/-- The component of the relative-chain projection in each degree is a cokernel. -/
noncomputable def relativeChainProjectionComponentIsCokernel (X : TopPair.{u}) (i : ℕ) :
    IsColimit (CokernelCofork.ofπ
      (f := ((chainPairFunctor R).obj X).hom.f i)
      ((relativeChainProjection R X).f i) (by
      have h := congrArg (fun q ↦ q.f i)
        (subspaceChainMap_relativeChainProjection R X)
      change ((chainPairFunctor R).obj X).hom.f i ≫
        (relativeChainProjection R X).f i = 0 at h
      exact h)) :=
  CokernelCofork.mapIsColimit _
    (cokernelIsCokernel ((chainPairFunctor R).obj X).hom)
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) i)

/-- A component of the ordinary singular prism, descended to relative chains. -/
noncomputable def relativeChainHomotopyComponent (H : TopPair.Homotopy f g) (i j : ℕ) :
    ((relativeChainFunctor R).obj X).X i ⟶
      ((relativeChainFunctor R).obj Y).X j :=
  (relativeChainProjectionComponentIsCokernel (R := R) X i).desc
    (CokernelCofork.ofπ
      ((H.fst.singularChainComplexFunctorObjMap (ModuleCat.of R R)).hom i j ≫
        (relativeChainProjection R Y).f j) (by
        change ((((singularChainComplexFunctor (ModuleCat.{u} R)).obj
            (ModuleCat.of R R)).map X.map).f i ≫
          (H.fst.singularChainComplexFunctorObjMap (ModuleCat.of R R)).hom i j) ≫
            (relativeChainProjection R Y).f j = 0
        rw [TopCat.Homotopy.singularChainHomotopy_hom_naturality
            H.fst H.snd X.map Y.map H.w (ModuleCat.of R R) i j,
          Category.assoc]
        have hz :
            ((((singularChainComplexFunctor (ModuleCat.{u} R)).obj
              (ModuleCat.of R R)).map Y.map).f j ≫
                (relativeChainProjection R Y).f j) = 0 :=
          congrArg (fun q ↦ q.f j) (subspaceChainMap_relativeChainProjection R Y)
        rw [hz, comp_zero]))

set_option backward.isDefEq.respectTransparency false in
lemma relativeChainHomotopyComponent_zero (H : TopPair.Homotopy f g)
    (i j : ℕ) (hij : ¬(ComplexShape.down ℕ).Rel j i) :
    relativeChainHomotopyComponent (R := R) H i j = 0 := by
  apply Cofork.IsColimit.hom_ext
    (relativeChainProjectionComponentIsCokernel (R := R) X i)
  rw [relativeChainHomotopyComponent, Cofork.IsColimit.π_desc]
  simp only [CokernelCofork.π_ofπ, comp_zero]
  rw [(H.fst.singularChainComplexFunctorObjMap (ModuleCat.of R R)).zero i j hij,
    zero_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma relativeChainHomotopyComponent_fac (H : TopPair.Homotopy f g)
    (i j : ℕ) :
    (relativeChainProjection R X).f i ≫
        relativeChainHomotopyComponent (R := R) H i j =
      (H.fst.singularChainComplexFunctorObjMap (ModuleCat.of R R)).hom i j ≫
        (relativeChainProjection R Y).f j := by
  unfold relativeChainHomotopyComponent
  exact (Cofork.IsColimit.π_desc
      (relativeChainProjectionComponentIsCokernel (R := R) X i)
      (t := CokernelCofork.ofπ
        ((H.fst.singularChainComplexFunctorObjMap (ModuleCat.of R R)).hom i j ≫
          (relativeChainProjection R Y).f j) _)).trans
    (CokernelCofork.π_ofπ _ _ _)

@[reassoc]
lemma relativeChainProjection_naturality (a : X ⟶ Y) :
    relativeChainProjection R X ≫ (relativeChainFunctor R).map a =
      ((singularChainComplexFunctor (ModuleCat.{u} R)).obj
          (ModuleCat.of R R)).map (TopPair.Hom.fst a) ≫ relativeChainProjection R Y := by
  change relativeChainProjection R X ≫ (relativeChainFunctor R).map a =
    ((chainPairFunctor R).map a).right ≫ relativeChainProjection R Y
  exact ((coker.π (C := ChainCategory R)).naturality
    ((chainPairFunctor R).map a)).symm

lemma relativeChainHomotopy_dNext_fac (H : TopPair.Homotopy f g) (i : ℕ) :
    (relativeChainProjection R X).f i ≫
        dNext i (relativeChainHomotopyComponent (R := R) H) =
      dNext i
          (H.fst.singularChainComplexFunctorObjMap (ModuleCat.of R R)).hom ≫
        (relativeChainProjection R Y).f i := by
  calc
    _ = dNext i (fun p q ↦
        (relativeChainProjection R X).f p ≫
          relativeChainHomotopyComponent (R := R) H p q) :=
      (dNext_comp_left (relativeChainProjection R X)
        (relativeChainHomotopyComponent (R := R) H) i).symm
    _ = dNext i (fun p q ↦
        (H.fst.singularChainComplexFunctorObjMap (ModuleCat.of R R)).hom p q ≫
          (relativeChainProjection R Y).f q) := by
      congr 1
      funext p q
      exact relativeChainHomotopyComponent_fac H p q
    _ = _ := dNext_comp_right
      (H.fst.singularChainComplexFunctorObjMap (ModuleCat.of R R)).hom
      (relativeChainProjection R Y) i

lemma relativeChainHomotopy_prevD_fac (H : TopPair.Homotopy f g) (i : ℕ) :
    (relativeChainProjection R X).f i ≫
        prevD i (relativeChainHomotopyComponent (R := R) H) =
      prevD i
          (H.fst.singularChainComplexFunctorObjMap (ModuleCat.of R R)).hom ≫
        (relativeChainProjection R Y).f i := by
  calc
    _ = prevD i (fun p q ↦
        (relativeChainProjection R X).f p ≫
          relativeChainHomotopyComponent (R := R) H p q) :=
      (prevD_comp_left (relativeChainProjection R X)
        (relativeChainHomotopyComponent (R := R) H) i).symm
    _ = prevD i (fun p q ↦
        (H.fst.singularChainComplexFunctorObjMap (ModuleCat.of R R)).hom p q ≫
          (relativeChainProjection R Y).f q) := by
      congr 1
      funext p q
      exact relativeChainHomotopyComponent_fac H p q
    _ = _ := prevD_comp_right
      (H.fst.singularChainComplexFunctorObjMap (ModuleCat.of R R)).hom
      (relativeChainProjection R Y) i

set_option backward.isDefEq.respectTransparency false in
/-- A homotopy of maps of topological pairs induces a chain homotopy on relative singular
chains. -/
noncomputable def relativeChainHomotopy (H : TopPair.Homotopy f g) :
    _root_.Homotopy ((relativeChainFunctor R).map f)
      ((relativeChainFunctor R).map g) where
  hom := relativeChainHomotopyComponent (R := R) H
  zero := relativeChainHomotopyComponent_zero H
  comm i := by
    apply Cofork.IsColimit.hom_ext
      (relativeChainProjectionComponentIsCokernel (R := R) X i)
    simp only [CokernelCofork.π_ofπ, Preadditive.comp_add]
    rw [relativeChainHomotopy_dNext_fac H i,
      relativeChainHomotopy_prevD_fac H i]
    have hf := congrArg (fun q ↦ q.f i)
      (relativeChainProjection_naturality (R := R) f)
    have hg := congrArg (fun q ↦ q.f i)
      (relativeChainProjection_naturality (R := R) g)
    change (relativeChainProjection R X).f i ≫
        ((relativeChainFunctor R).map f).f i =
      (((singularChainComplexFunctor (ModuleCat.{u} R)).obj
        (ModuleCat.of R R)).map (TopPair.Hom.fst f)).f i ≫
          (relativeChainProjection R Y).f i at hf
    change (relativeChainProjection R X).f i ≫
        ((relativeChainFunctor R).map g).f i =
      (((singularChainComplexFunctor (ModuleCat.{u} R)).obj
        (ModuleCat.of R R)).map (TopPair.Hom.fst g)).f i ≫
          (relativeChainProjection R Y).f i at hg
    rw [hf, hg,
      (H.fst.singularChainComplexFunctorObjMap (ModuleCat.of R R)).comm i,
      Preadditive.add_comp, Preadditive.add_comp]

/-- Homotopic maps of topological pairs induce equal maps on relative singular homology. -/
theorem congr_relativeHomologyMap (H : TopPair.Homotopy f g) (n : ℕ) :
    relativeHomologyMap R n f = relativeHomologyMap R n g := by
  change (HomologicalComplex.homologyMap ((relativeChainFunctor R).map f) n).hom =
    (HomologicalComplex.homologyMap ((relativeChainFunctor R).map g) n).hom
  exact congrArg ModuleCat.Hom.hom
    ((relativeChainHomotopy (R := R) H).homologyMap_eq n)

/-- Homotopic maps of pairs send each relative homology class to the same class. -/
theorem relativeHomologyMap_apply_eq (H : TopPair.Homotopy f g) (n : ℕ)
    (z : RelativeHomology R X n) :
    relativeHomologyMap R n f z = relativeHomologyMap R n g z := by
  rw [congr_relativeHomologyMap H n]

end TopPair.Homotopy
