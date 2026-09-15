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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularCoverSmall
public import Mathlib.Algebra.Category.ModuleCat.Colimits

import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularExcisionOpenCover

/-!
# Small singular chains with rational coefficients

This file transports the integral subdivision homotopy to rational simplicial chains.  The
transport is constructed directly from the universal bases of the two simplicial chain
complexes.  In particular, it does not assume a universal-coefficient theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace AlgebraicTopology.Singular

/-- Rational chains on a simplicial set. -/
abbrev RationalSimplicialChainComplex (X : SSet.{0}) :
    ChainComplex (ModuleCat ℚ) ℕ :=
  X.chainComplex (ModuleCat.of ℚ ℚ)

/-- The underlying additive group of a rational module. -/
abbrev rationalForget := forget₂ (ModuleCat ℚ) AddCommGrpCat

@[simp]
lemma moduleCat_toSpanSingleton_apply_one (M : ModuleCat ℚ) (v : M) :
    (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ M v)).hom 1 = v := by
  change (1 : ℚ) • v = v
  simp

/-- The coefficient map from integral to rational chains in one degree. -/
def integralToRationalChainComponent (X : SSet.{0}) (n : ℕ) :
    (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      rationalForget.obj ((RationalSimplicialChainComplex X).X n) :=
  (X.isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) n).desc
    (Cofan.mk _ fun x ↦
      AddCommGrpCat.ofHom (Int.castAddHom ℚ) ≫
        rationalForget.map (X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x))

@[reassoc]
lemma iota_integralToRationalChainComponent (X : SSet.{0}) (n : ℕ)
    (x : X _⦋n⦌) :
    X.ιChainComplex (R := AddCommGrpCat.of ℤ) x ≫
        integralToRationalChainComponent X n =
      AddCommGrpCat.ofHom (Int.castAddHom ℚ) ≫
        rationalForget.map (X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x) :=
  (X.isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) n).fac _ (Discrete.mk x)

/-- Extend an integral map between free simplicial-chain groups rational-linearly. -/
def rationalizeSimplicialChainComponent (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    (RationalSimplicialChainComplex X).X n ⟶
      (RationalSimplicialChainComplex Y).X m :=
  (X.isColimitChainComplexXCofan (ModuleCat.of ℚ ℚ) n).desc
    (Cofan.mk _ fun x ↦ ModuleCat.ofHom <|
      LinearMap.toSpanSingleton ℚ _ <|
        (show (RationalSimplicialChainComplex Y).X m from
          (integralToRationalChainComponent Y m).hom
            (f.hom ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1))))

@[reassoc]
lemma iota_rationalizeSimplicialChainComponent
    (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m)
    (x : X _⦋n⦌) :
    X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x ≫
        rationalizeSimplicialChainComponent X Y n m f =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ <|
        (show (RationalSimplicialChainComplex Y).X m from
          (integralToRationalChainComponent Y m).hom
            (f.hom ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1)))) :=
  (X.isColimitChainComplexXCofan (ModuleCat.of ℚ ℚ) n).fac _ (Discrete.mk x)

lemma integralToRationalChainComponent_naturality
    (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    integralToRationalChainComponent X n ≫
        rationalForget.map (rationalizeSimplicialChainComponent X Y n m f) =
      f ≫ integralToRationalChainComponent Y m := by
  refine (X.isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) n).hom_ext fun x ↦ ?_
  change X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as ≫
      (integralToRationalChainComponent X n ≫
        rationalForget.map (rationalizeSimplicialChainComponent X Y n m f)) =
    X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as ≫
      (f ≫ integralToRationalChainComponent Y m)
  apply AddCommGrpCat.int_hom_ext
  have hx := ConcreteCategory.congr_hom
    (iota_integralToRationalChainComponent X n x.as) 1
  have hf := ConcreteCategory.congr_hom
    (iota_rationalizeSimplicialChainComponent X Y n m f x.as) 1
  change (rationalizeSimplicialChainComponent X Y n m f).hom
      ((integralToRationalChainComponent X n).hom
        ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as).hom 1)) = _
  change (integralToRationalChainComponent X n).hom
      ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as).hom 1) =
    (X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x.as).hom 1 at hx
  rw [hx]
  simp only [ConcreteCategory.comp_apply] at hf ⊢
  simpa using hf

lemma rationalizeSimplicialChainComponent_comp
    (X Y Z : SSet.{0}) (n m k : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m)
    (g : (Y.chainComplex (AddCommGrpCat.of ℤ)).X m ⟶
      (Z.chainComplex (AddCommGrpCat.of ℤ)).X k) :
    rationalizeSimplicialChainComponent X Z n k (f ≫ g) =
      rationalizeSimplicialChainComponent X Y n m f ≫
        rationalizeSimplicialChainComponent Y Z m k g := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_rationalizeSimplicialChainComponent,
    iota_rationalizeSimplicialChainComponent_assoc]
  ext
  have h := ConcreteCategory.congr_hom
    (integralToRationalChainComponent_naturality Y Z m k g)
    (f.hom ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1))
  simp only [ConcreteCategory.comp_apply] at h ⊢
  simpa using h.symm

lemma rationalizeSimplicialChainComponent_id (X : SSet.{0}) (n : ℕ) :
    rationalizeSimplicialChainComponent X X n n (𝟙 _) = 𝟙 _ := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_rationalizeSimplicialChainComponent]
  ext
  simp only [Category.comp_id,
    ConcreteCategory.id_apply]
  have hx := ConcreteCategory.congr_hom
    (iota_integralToRationalChainComponent X n x) 1
  simp only [ConcreteCategory.comp_apply] at hx
  simpa using hx

lemma rationalizeSimplicialChainComponent_zero
    (X Y : SSet.{0}) (n m : ℕ) :
    rationalizeSimplicialChainComponent X Y n m 0 = 0 := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_rationalizeSimplicialChainComponent]
  ext
  simp

lemma rationalizeSimplicialChainComponent_add
    (X Y : SSet.{0}) (n m : ℕ)
    (f g : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    rationalizeSimplicialChainComponent X Y n m (f + g) =
      rationalizeSimplicialChainComponent X Y n m f +
        rationalizeSimplicialChainComponent X Y n m g := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_rationalizeSimplicialChainComponent, Preadditive.comp_add,
    iota_rationalizeSimplicialChainComponent,
    iota_rationalizeSimplicialChainComponent]
  ext
  simp

lemma rationalizeSimplicialChainComponent_neg
    (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    rationalizeSimplicialChainComponent X Y n m (-f) =
      -rationalizeSimplicialChainComponent X Y n m f := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_rationalizeSimplicialChainComponent, Preadditive.comp_neg,
    iota_rationalizeSimplicialChainComponent]
  ext
  simp

/-- The integral-to-rational coefficient map commutes with the simplicial differential. -/
lemma integralToRationalChainComponent_comm_d (X : SSet.{0}) (n : ℕ) :
    integralToRationalChainComponent X (n + 1) ≫
        rationalForget.map ((RationalSimplicialChainComplex X).d (n + 1) n) =
      (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
        integralToRationalChainComponent X n := by
  refine (X.isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) (n + 1)).hom_ext fun x ↦ ?_
  change X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as ≫
      (integralToRationalChainComponent X (n + 1) ≫
        rationalForget.map ((RationalSimplicialChainComplex X).d (n + 1) n)) =
    X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as ≫
      ((X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
        integralToRationalChainComponent X n)
  rw [← Category.assoc, iota_integralToRationalChainComponent, Category.assoc,
    ← Functor.map_comp, SSet.ιChainComplex_d, ← Category.assoc, SSet.ιChainComplex_d,
    Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, iota_integralToRationalChainComponent]
  simp only [Functor.map_sum, Functor.map_zsmul]
  rw [Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.comp_zsmul]

/-- Rationalization sends the integral simplicial differential to the rational differential. -/
lemma rationalizeSimplicialChainComponent_d (X : SSet.{0}) (n : ℕ) :
    rationalizeSimplicialChainComponent X X (n + 1) n
        ((X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n) =
      (RationalSimplicialChainComplex X).d (n + 1) n := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_rationalizeSimplicialChainComponent]
  ext
  change (LinearMap.toSpanSingleton ℚ _ _) 1 = _
  rw [LinearMap.toSpanSingleton_apply_one]
  simp only [ConcreteCategory.comp_apply]
  change (integralToRationalChainComponent X n).hom
      (((X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n).hom
        ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1)) =
    ((RationalSimplicialChainComplex X).d (n + 1) n).hom
      ((X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x).hom 1)
  have h := ConcreteCategory.congr_hom
    (integralToRationalChainComponent_comm_d X n)
    ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1)
  have hx := ConcreteCategory.congr_hom
    (iota_integralToRationalChainComponent X (n + 1) x) 1
  simp only [ConcreteCategory.comp_apply] at h hx ⊢
  rw [hx] at h
  exact h.symm

/-- Rationalization of a chain map between integral simplicial chains. -/
def rationalizeSimplicialChainMap (X Y : SSet.{0})
    (f : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)) :
    RationalSimplicialChainComplex X ⟶ RationalSimplicialChainComplex Y where
  f n := rationalizeSimplicialChainComponent X Y n n (f.f n)
  comm' i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    subst i
    rw [← rationalizeSimplicialChainComponent_d Y j,
      ← rationalizeSimplicialChainComponent_comp, f.comm,
      rationalizeSimplicialChainComponent_comp,
      rationalizeSimplicialChainComponent_d]

@[simp]
lemma rationalizeSimplicialChainMap_f (X Y : SSet.{0})
    (f : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)) (n : ℕ) :
    (rationalizeSimplicialChainMap X Y f).f n =
      rationalizeSimplicialChainComponent X Y n n (f.f n) :=
  rfl

lemma rationalizeSimplicialChainMap_id (X : SSet.{0}) :
    rationalizeSimplicialChainMap X X (𝟙 _) = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun n ↦ rationalizeSimplicialChainComponent_id X n

lemma rationalizeSimplicialChainMap_comp (X Y Z : SSet.{0})
    (f : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ))
    (g : Y.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Z.chainComplex (AddCommGrpCat.of ℤ)) :
    rationalizeSimplicialChainMap X Z (f ≫ g) =
      rationalizeSimplicialChainMap X Y f ≫
        rationalizeSimplicialChainMap Y Z g :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    rationalizeSimplicialChainComponent_comp X Y Z n n n (f.f n) (g.f n)

lemma rationalizeSimplicialChainMap_add (X Y : SSet.{0})
    (f g : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)) :
    rationalizeSimplicialChainMap X Y (f + g) =
      rationalizeSimplicialChainMap X Y f +
        rationalizeSimplicialChainMap X Y g :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    rationalizeSimplicialChainComponent_add X Y n n (f.f n) (g.f n)

lemma rationalizeSimplicialChainMap_zero (X Y : SSet.{0}) :
    rationalizeSimplicialChainMap X Y 0 = 0 :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    rationalizeSimplicialChainComponent_zero X Y n n

/-- Rationalization preserves a chain homotopy between integral simplicial chain maps. -/
def rationalizeSimplicialChainHomotopy (X Y : SSet.{0})
    {f g : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)} (h : Homotopy f g) :
    Homotopy (rationalizeSimplicialChainMap X Y f)
      (rationalizeSimplicialChainMap X Y g) where
  hom i j := rationalizeSimplicialChainComponent X Y i j (h.hom i j)
  zero i j hij := by
    rw [h.zero i j hij, rationalizeSimplicialChainComponent_zero]
  comm i := by
    cases i with
    | zero =>
        have hh := congrArg
          (rationalizeSimplicialChainComponent X Y 0 0) (h.comm 0)
        rw [Homotopy.dNext_zero_chainComplex,
          Homotopy.prevD_chainComplex] at hh ⊢
        simp only [rationalizeSimplicialChainComponent_add,
          rationalizeSimplicialChainComponent_comp,
          rationalizeSimplicialChainComponent_d, zero_add] at hh
        change rationalizeSimplicialChainComponent X Y 0 0 (f.f 0) =
          0 + rationalizeSimplicialChainComponent X Y 0 1 (h.hom 0 1) ≫
            (RationalSimplicialChainComplex Y).d 1 0 +
              rationalizeSimplicialChainComponent X Y 0 0 (g.f 0)
        simpa only [zero_add] using hh
    | succ n =>
        have hh := congrArg
          (rationalizeSimplicialChainComponent X Y (n + 1) (n + 1))
            (h.comm (n + 1))
        rw [Homotopy.dNext_succ_chainComplex,
          Homotopy.prevD_chainComplex] at hh ⊢
        simp only [rationalizeSimplicialChainComponent_add,
          rationalizeSimplicialChainComponent_comp,
          rationalizeSimplicialChainComponent_d] at hh
        exact hh

/-- Rationalization preserves a chain-homotopy equivalence of simplicial chain complexes. -/
def rationalizeSimplicialChainHomotopyEquiv (X Y : SSet.{0})
    (e : HomotopyEquiv (X.chainComplex (AddCommGrpCat.of ℤ))
      (Y.chainComplex (AddCommGrpCat.of ℤ))) :
    HomotopyEquiv (RationalSimplicialChainComplex X)
      (RationalSimplicialChainComplex Y) where
  hom := rationalizeSimplicialChainMap X Y e.hom
  inv := rationalizeSimplicialChainMap Y X e.inv
  homotopyHomInvId :=
    (Homotopy.ofEq (rationalizeSimplicialChainMap_comp X Y X e.hom e.inv).symm).trans
      ((rationalizeSimplicialChainHomotopy X X e.homotopyHomInvId).trans
        (Homotopy.ofEq (rationalizeSimplicialChainMap_id X)))
  homotopyInvHomId :=
    (Homotopy.ofEq (rationalizeSimplicialChainMap_comp Y X Y e.inv e.hom).symm).trans
      ((rationalizeSimplicialChainHomotopy Y Y e.homotopyInvHomId).trans
        (Homotopy.ofEq (rationalizeSimplicialChainMap_id Y)))

/-- Rationalization of an integral chain map induced by a simplicial map is the corresponding
rational chain map. -/
lemma rationalizeSimplicialChainComponent_chainComplexMap
    {X Y : SSet.{0}} (f : X ⟶ Y) (n : ℕ) :
    rationalizeSimplicialChainComponent X Y n n
        ((SSet.chainComplexMap f (AddCommGrpCat.of ℤ)).f n) =
      (SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)).f n := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_rationalizeSimplicialChainComponent,
    SSet.ι_chainComplexMap_f]
  ext
  change (LinearMap.toSpanSingleton ℚ _ _) 1 = _
  rw [LinearMap.toSpanSingleton_apply_one]
  change (integralToRationalChainComponent Y n).hom
      (((SSet.chainComplexMap f (AddCommGrpCat.of ℤ)).f n).hom
        ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1)) =
    (Y.ιChainComplex (R := ModuleCat.of ℚ ℚ) (f.app _ x)).hom 1
  have hf := ConcreteCategory.congr_hom
    (SSet.ι_chainComplexMap_f X Y f (AddCommGrpCat.of ℤ) x) 1
  have hcoeff := ConcreteCategory.congr_hom
    (iota_integralToRationalChainComponent Y n (f.app _ x)) 1
  simp only [ConcreteCategory.comp_apply] at hf hcoeff
  rw [hf]
  exact hcoeff

lemma rationalizeSimplicialChainMap_chainComplexMap
    {X Y : SSet.{0}} (f : X ⟶ Y) :
    rationalizeSimplicialChainMap X Y
        (SSet.chainComplexMap f (AddCommGrpCat.of ℤ)) =
      SSet.chainComplexMap f (ModuleCat.of ℚ ℚ) :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    rationalizeSimplicialChainComponent_chainComplexMap f n

section RationalSmallChains

variable {ι : Type} (X : TopCat.{0}) (U : ι → Set X)

/-- Rational chains generated by singular simplices subordinate to one member of a cover. -/
abbrev CoverSmallRationalSingularChainComplex :
    ChainComplex (ModuleCat ℚ) ℕ :=
  (coverSmallSingularSubcomplex X U : SSet).chainComplex (ModuleCat.of ℚ ℚ)

/-- Inclusion of cover-small rational singular chains into all rational singular chains. -/
def coverSmallRationalSingularChainInclusion :
    CoverSmallRationalSingularChainComplex X U ⟶
      (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ) :=
  SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι (ModuleCat.of ℚ ℚ)

instance coverSmallRationalSingularChainInclusion_mono :
    Mono (coverSmallRationalSingularChainInclusion X U) := by
  dsimp [coverSmallRationalSingularChainInclusion, SSet.chainComplexMap,
    SSet.chainComplexFunctor]
  apply +allowSynthFailures Functor.map_mono
  apply +allowSynthFailures Functor.map_mono
  dsimp [SSet, SimplicialObject.whiskering, SimplicialObject]
  infer_instance

/-- The proven integral subdivision-and-prism homotopy transports to rational coefficients:
the all-open-cover small-chain theorem with rational coefficients. -/
theorem coverSmallRationalChainApproximation_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomologicalComplex.homotopyEquivalences (ModuleCat ℚ) (ComplexShape.down ℕ)
      (coverSmallRationalSingularChainInclusion X U) := by
  let eZ := coverSmallChainHomotopyEquiv_of_openCover X U hUopen hUcover
  refine ⟨rationalizeSimplicialChainHomotopyEquiv
    (coverSmallSingularSubcomplex X U : SSet) (TopCat.toSSet.obj X) eZ, ?_⟩
  change rationalizeSimplicialChainMap
      (coverSmallSingularSubcomplex X U : SSet) (TopCat.toSSet.obj X) eZ.hom =
    coverSmallRationalSingularChainInclusion X U
  rw [show eZ.hom = coverSmallIntegralSingularChainInclusion X U from
    coverSmallChainHomotopyEquiv_of_openCover_hom X U hUopen hUcover]
  exact rationalizeSimplicialChainMap_chainComplexMap
    (coverSmallSingularSubcomplex X U).ι

/-- A selected rational small-chain homotopy equivalence for an open cover. -/
def coverSmallRationalChainHomotopyEquiv_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomotopyEquiv (CoverSmallRationalSingularChainComplex X U)
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)) :=
  (coverSmallRationalChainApproximation_of_openCover X U hUopen hUcover).choose

lemma coverSmallRationalChainHomotopyEquiv_of_openCover_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (coverSmallRationalChainHomotopyEquiv_of_openCover X U hUopen hUcover).hom =
      coverSmallRationalSingularChainInclusion X U :=
  (coverSmallRationalChainApproximation_of_openCover X U hUopen hUcover).choose_spec

/-- Rational small-chain inclusion induces an isomorphism on homology in every degree. -/
def coverSmallRationalSingularHomologyIso_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    (CoverSmallRationalSingularChainComplex X U).homology n ≅
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).homology n :=
  (coverSmallRationalChainHomotopyEquiv_of_openCover X U hUopen hUcover).toHomologyIso n

lemma coverSmallRationalSingularHomologyIso_of_openCover_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    (coverSmallRationalSingularHomologyIso_of_openCover X U hUopen hUcover n).hom =
      HomologicalComplex.homologyMap
        (coverSmallRationalSingularChainInclusion X U) n := by
  dsimp [coverSmallRationalSingularHomologyIso_of_openCover]
  change HomologicalComplex.homologyMap
      (coverSmallRationalChainHomotopyEquiv_of_openCover X U hUopen hUcover).hom n = _
  rw [coverSmallRationalChainHomotopyEquiv_of_openCover_hom]

end RationalSmallChains

end AlgebraicTopology.Singular
