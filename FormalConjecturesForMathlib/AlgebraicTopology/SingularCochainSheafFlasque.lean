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

public import FormalConjecturesForMathlib.AlgebraicTopology.SingularCochainSheaf
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Sheaves.Flasque

import FormalConjecturesForMathlib.AlgebraicTopology.SingularCochainFlasque
import Mathlib.Topology.Sheaves.SheafOfFunctions

/-!
# Descent for singular cochains

Singular cochains in every degree are arbitrary functions on singular simplices. This gives
existence of gluings for compatible raw cochains, global raw representatives for the first plus
construction, and flasqueness of that first plus presheaf. The first plus construction is only the
separated reflection in general. Its flasqueness is therefore not a sheaf-level acyclicity or
derived-global-sections comparison theorem.

In degree zero, singular simplices are points and the raw presheaf is already the sheaf of all
functions. Consequently its sheafification is flasque in degree zero. No positive-degree
flasqueness claim is made for the second plus construction or abstract sheafification.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped Simplicial

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopCat.{u})

/-- Singular `n`-simplices in an open subset. -/
abbrev OpenSimplex (U : (Opens X)ᵒᵖ) (n : ℕ) :=
  (TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop)).obj
    (Opposite.op (SimplexCategory.mk n))

/-- The singular chain consisting of one simplex with coefficient one. -/
noncomputable def singularChainOfSimplex (U : (Opens X)ᵒᵖ) (n : ℕ)
    (s : OpenSimplex X U n) : OpenChains R X U n :=
  (Sigma.ι (fun _ : OpenSimplex X U n ↦ ModuleCat.of R R) s).hom 1

/-- Evaluate a singular cochain on every basis simplex. -/
def singularCochainToSimplexFunction (U : (Opens X)ᵒᵖ) (n : ℕ) :
    OpenCochains R X U n →ₗ[R] (OpenSimplex X U n → R) where
  toFun φ s := φ (singularChainOfSimplex R X U n s)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Construct a singular cochain from its values on basis simplices. -/
noncomputable def singularCochainOfSimplexFunction (U : (Opens X)ᵒᵖ) (n : ℕ) :
    (OpenSimplex X U n → R) →ₗ[R] OpenCochains R X U n where
  toFun f := by
    change Module.Dual R
      ((sigmaObj (C := ModuleCat.{u} R)
        fun _ : OpenSimplex X U n ↦ ModuleCat.of R R) : Type u)
    exact (Sigma.desc fun s ↦ ModuleCat.ofHom <|
      (LinearMap.ringLmapEquivSelf R R R).symm (f s)).hom
  map_add' f g := by
    change (Sigma.desc fun s : OpenSimplex X U n ↦ ModuleCat.ofHom <|
      (LinearMap.ringLmapEquivSelf R R R).symm ((f + g) s)).hom =
      ((Sigma.desc fun s : OpenSimplex X U n ↦ ModuleCat.ofHom <|
          (LinearMap.ringLmapEquivSelf R R R).symm (f s)) +
        (Sigma.desc fun s : OpenSimplex X U n ↦ ModuleCat.ofHom <|
          (LinearMap.ringLmapEquivSelf R R R).symm (g s))).hom
    exact congrArg ModuleCat.Hom.hom <| Sigma.hom_ext _ _ fun s ↦ by
      rw [Preadditive.comp_add, Sigma.ι_desc, Sigma.ι_desc, Sigma.ι_desc]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      change r * (f s + g s) = r * f s + r * g s
      exact mul_add r (f s) (g s)
  map_smul' a f := by
    change (Sigma.desc fun s : OpenSimplex X U n ↦ ModuleCat.ofHom <|
      (LinearMap.ringLmapEquivSelf R R R).symm ((a • f) s)).hom =
      (a • (Sigma.desc fun s : OpenSimplex X U n ↦ ModuleCat.ofHom <|
        (LinearMap.ringLmapEquivSelf R R R).symm (f s))).hom
    exact congrArg ModuleCat.Hom.hom <| Sigma.hom_ext _ _ fun s ↦ by
      rw [Linear.comp_smul, Sigma.ι_desc, Sigma.ι_desc]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      change r * (a * f s) = a * (r * f s)
      ring

@[simp]
lemma singularCochainToSimplexFunction_ofFunction (U : (Opens X)ᵒᵖ) (n : ℕ)
    (f : OpenSimplex X U n → R) :
    singularCochainToSimplexFunction R X U n
      (singularCochainOfSimplexFunction R X U n f) = f := by
  ext s
  change (ModuleCat.Hom.hom
    (Sigma.ι (fun _ : OpenSimplex X U n ↦ ModuleCat.of R R) s ≫
      Sigma.desc (fun t : OpenSimplex X U n ↦ ModuleCat.ofHom <|
        (LinearMap.ringLmapEquivSelf R R R).symm (f t)))) 1 = f s
  rw [Sigma.ι_desc]
  exact (LinearMap.ringLmapEquivSelf R R R).apply_symm_apply (f s)

@[simp]
lemma singularCochainOfSimplexFunction_toFunction (U : (Opens X)ᵒᵖ) (n : ℕ)
    (φ : OpenCochains R X U n) :
    singularCochainOfSimplexFunction R X U n
      (singularCochainToSimplexFunction R X U n φ) = φ := by
  change Module.Dual R
    ((sigmaObj (C := ModuleCat.{u} R)
      fun _ : OpenSimplex X U n ↦ ModuleCat.of R R) : Type u) at φ
  dsimp [singularCochainOfSimplexFunction, singularCochainToSimplexFunction,
    singularChainOfSimplex]
  change (Sigma.desc (fun s : OpenSimplex X U n ↦ ModuleCat.ofHom <|
      (LinearMap.ringLmapEquivSelf R R R).symm
        (φ ((Sigma.ι (fun _ : OpenSimplex X U n ↦ ModuleCat.of R R) s).hom 1)))).hom = φ
  exact congrArg ModuleCat.Hom.hom <| Sigma.hom_ext _ _ fun s ↦ by
    rw [Sigma.ι_desc]
    apply ModuleCat.hom_ext
    change (LinearMap.ringLmapEquivSelf R R R).symm
      (φ ((Sigma.ι (fun _ : OpenSimplex X U n ↦ ModuleCat.of R R) s).hom 1)) =
      (Sigma.ι (fun _ : OpenSimplex X U n ↦ ModuleCat.of R R) s ≫ ModuleCat.ofHom φ).hom
    apply (LinearMap.ringLmapEquivSelf R R R).injective
    rw [LinearEquiv.apply_symm_apply]
    rfl

/-- Singular cochains are precisely arbitrary functions on singular simplices. -/
noncomputable def singularCochainEquivSimplexFunction (U : (Opens X)ᵒᵖ) (n : ℕ) :
    OpenCochains R X U n ≃ₗ[R] (OpenSimplex X U n → R) := by
  refine LinearEquiv.ofLinearMap (singularCochainToSimplexFunction R X U n)
    (singularCochainOfSimplexFunction R X U n) ?_ ?_
  · ext f s
    exact congrFun (singularCochainToSimplexFunction_ofFunction R X U n f) s
  · ext φ c
    exact congrArg (fun f ↦ f c)
      (singularCochainOfSimplexFunction_toFunction R X U n φ)

/-- An inclusion of open subsets sends a singular simplex to the same simplex in the larger
open subset. -/
def openSimplexMap {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ) :
    OpenSimplex X V n → OpenSimplex X U n :=
  (TopCat.toSSet.map ((Opens.toTopCat X).map i.unop)).app
    (Opposite.op (SimplexCategory.mk n))

/-- Basis singular chains are natural under inclusion of open subsets. -/
lemma singularChainOfSimplex_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (n : ℕ) (s : OpenSimplex X V n) :
    (((openSingularChainComplexFunctor R X).map i.unop).f n).hom
        (singularChainOfSimplex R X V n s) =
      singularChainOfSimplex R X U n (openSimplexMap X i n s) := by
  have hs := SSet.ι_chainComplexMap_f _ _
    (TopCat.toSSet.map ((Opens.toTopCat X).map i.unop))
    (ModuleCat.of R R) s
  exact congrArg (fun g ↦ g.hom 1) hs

/-- Under the function model for cochains, restriction is precomposition with the inclusion on
singular simplices. -/
lemma singularCochainToSimplexFunction_naturality
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ)
    (φ : OpenCochains R X U n) :
    singularCochainToSimplexFunction R X V n
        ((singularCochainPresheaf R X n).map i φ) =
      (singularCochainToSimplexFunction R X U n φ) ∘
        openSimplexMap X i n := by
  ext s
  change φ ((((openSingularChainComplexFunctor R X).map i.unop).f n).hom
    (singularChainOfSimplex R X V n s)) =
    φ (singularChainOfSimplex R X U n (openSimplexMap X i n s))
  rw [singularChainOfSimplex_naturality]

/-- Two simplices in open subsets which become equal in a containing open subset have a common
lift to the intersection. -/
lemma exists_openSimplex_inf_of_eq {U A B : Opens X} (i : A ⟶ U) (j : B ⟶ U)
    (n : ℕ) (s : OpenSimplex X (.op A) n) (t : OpenSimplex X (.op B) n)
    (h : openSimplexMap X i.op n s = openSimplexMap X j.op n t) :
    ∃ r : OpenSimplex X (.op (A ⊓ B)) n,
      openSimplexMap X (homOfLE inf_le_left).op n r = s ∧
        openSimplexMap X (homOfLE inf_le_right).op n r = t := by
  let m := Opposite.op (SimplexCategory.mk n)
  let fs := (TopCat.of A).toSSetObjEquiv m s
  let ft := (TopCat.of B).toSSetObjEquiv m t
  have hst : ∀ z, (fs z).1 = (ft z).1 := fun z ↦
    congrArg Subtype.val (congrArg (fun q ↦ (TopCat.of U).toSSetObjEquiv m q z) h)
  let f : C(stdSimplex ℝ (Fin (n + 1)), TopCat.of ↑(A ⊓ B)) :=
    ⟨fun z ↦ ⟨(fs z).1, (fs z).2, by rw [hst z]; exact (ft z).2⟩,
      Continuous.subtype_mk
        (continuous_subtype_val.comp fs.continuous) _⟩
  let r : OpenSimplex X (.op (A ⊓ B)) n :=
    (TopCat.of ↑(A ⊓ B)).toSSetObjEquiv m |>.symm f
  refine ⟨r, ?_, ?_⟩
  · apply (TopCat.of A).toSSetObjEquiv m |>.injective
    ext z
    rfl
  · apply (TopCat.of B).toSSetObjEquiv m |>.injective
    ext z
    exact hst z

/-- Compatible cochains on any family of open subsets extend to a cochain on the containing open
set. Compatibility is expressed on basis simplices after mapping them into the containing open.
No covering hypothesis is needed. -/
lemma exists_openCochain_of_compatibleOnSimplexBasis
    {U : (Opens X)ᵒᵖ} {ι : Type*} (V : ι → (Opens X)ᵒᵖ)
    (e : ∀ i, U ⟶ V i) (n : ℕ) (φ : ∀ i, OpenCochains R X (V i) n)
    (hφ : ∀ (i j) (s : OpenSimplex X (V i) n) (t : OpenSimplex X (V j) n),
      openSimplexMap X (e i) n s = openSimplexMap X (e j) n t →
        singularCochainToSimplexFunction R X (V i) n (φ i) s =
          singularCochainToSimplexFunction R X (V j) n (φ j) t) :
    ∃ ψ : OpenCochains R X U n,
      ∀ i, (singularCochainPresheaf R X n).map (e i) ψ = φ i := by
  classical
  let Lift (s : OpenSimplex X U n) :=
    Σ i, {t : OpenSimplex X (V i) n // openSimplexMap X (e i) n t = s}
  let f : OpenSimplex X U n → R := fun s ↦
    if hs : Nonempty (Lift s) then
      singularCochainToSimplexFunction R X (V hs.some.1) n (φ hs.some.1) hs.some.2
    else 0
  refine ⟨singularCochainOfSimplexFunction R X U n f, fun i ↦ ?_⟩
  apply (singularCochainEquivSimplexFunction R X (V i) n).injective
  change singularCochainToSimplexFunction R X (V i) n
      ((singularCochainPresheaf R X n).map (e i)
        (singularCochainOfSimplexFunction R X U n f)) =
    singularCochainToSimplexFunction R X (V i) n (φ i)
  ext s
  rw [singularCochainToSimplexFunction_naturality,
    singularCochainToSimplexFunction_ofFunction]
  change f (openSimplexMap X (e i) n s) = _
  let w : Lift (openSimplexMap X (e i) n s) := ⟨i, s, rfl⟩
  dsimp only [f]
  split
  · next hs =>
      exact hφ hs.some.1 i hs.some.2 s
        (hs.some.2.property.trans w.2.property.symm)
  · next hs => exact (hs ⟨w⟩).elim

/-- A compatible family of singular cochains over a covering sieve is the restriction of one
cochain on the covered open set. -/
lemma exists_openCochain_of_meq {U : Opens X}
    (S : (Opens.grothendieckTopology X).Cover U)
    (n : ℕ) (x : Meq (singularCochainPresheaf R X n) S) :
    ∃ φ : OpenCochains R X (.op U) n,
      ∀ I : S.Arrow, (singularCochainPresheaf R X n).map I.f.op φ = x I := by
  classical
  apply exists_openCochain_of_compatibleOnSimplexBasis R X
    (fun I : S.Arrow ↦ .op I.Y) (fun I ↦ I.f.op) n (fun I ↦ x I)
  intro I J s t hst
  obtain ⟨r, hrs, hrt⟩ := exists_openSimplex_inf_of_eq X I.f J.f n s t hst
  let rel : S.Relation := GrothendieckTopology.Cover.Relation.mk'
    { Z := I.Y ⊓ J.Y
      g₁ := homOfLE inf_le_left
      g₂ := homOfLE inf_le_right }
  have hrel := congrArg
    (fun ψ ↦ singularCochainToSimplexFunction R X (.op (I.Y ⊓ J.Y)) n ψ r)
    (x.condition rel)
  change singularCochainToSimplexFunction R X (.op (I.Y ⊓ J.Y)) n
      ((singularCochainPresheaf R X n).map (homOfLE inf_le_left).op (x I)) r =
    singularCochainToSimplexFunction R X (.op (I.Y ⊓ J.Y)) n
      ((singularCochainPresheaf R X n).map (homOfLE inf_le_right).op (x J)) r at hrel
  have hl := congrFun (singularCochainToSimplexFunction_naturality R X
    (homOfLE inf_le_left).op n (x I)) r
  have hr := congrFun (singularCochainToSimplexFunction_naturality R X
    (homOfLE inf_le_right).op n (x J)) r
  calc
    _ = singularCochainToSimplexFunction R X (.op I.Y) n (x I)
        (openSimplexMap X (homOfLE inf_le_left).op n r) := by rw [hrs]
    _ = singularCochainToSimplexFunction R X (.op (I.Y ⊓ J.Y)) n
        ((singularCochainPresheaf R X n).map
          (homOfLE inf_le_left).op (x I)) r := hl.symm
    _ = singularCochainToSimplexFunction R X (.op (I.Y ⊓ J.Y)) n
        ((singularCochainPresheaf R X n).map
          (homOfLE inf_le_right).op (x J)) r := hrel
    _ = singularCochainToSimplexFunction R X (.op J.Y) n (x J)
        (openSimplexMap X (homOfLE inf_le_right).op n r) := hr
    _ = _ := by rw [hrt]

/-- Every section of the first plus construction has a representative which is a single cochain
on the whole open set. This pointwise form avoids unfolding the large categorical type of the
plus map into a `Function.Surjective` proposition. -/
lemma singularCochain_toPlus_exists_rep (U : Opens X) (n : ℕ)
    (y : ToType (((Opens.grothendieckTopology X).plusObj
      (singularCochainPresheaf R X n)).obj (.op U))) :
    ∃ φ : OpenCochains R X (.op U) n,
      ((Opens.grothendieckTopology X).toPlus
        (singularCochainPresheaf R X n)).app (.op U) φ = y := by
  classical
  obtain ⟨S, x, hy⟩ := GrothendieckTopology.Plus.exists_rep y
  obtain ⟨φ, hφ⟩ := exists_openCochain_of_meq R X S n x
  let φ' : ToType ((singularCochainPresheaf R X n).obj (.op U)) := φ
  refine ⟨φ', ?_⟩
  rw [hy]
  calc
    _ = GrothendieckTopology.Plus.mk (Meq.mk S φ') :=
      GrothendieckTopology.Plus.toPlus_mk S φ'
    _ = GrothendieckTopology.Plus.mk x := by
      congr 1
      ext I
      exact hφ I

/-- The first plus construction of the singular-cochain presheaf is flasque. Although it is only
a separated presheaf in general, every one of its sections has a global cochain representative,
so raw cochain extension proves surjectivity of all its restriction maps. -/
instance singularCochainPlus_isFlasque (n : ℕ) :
    TopCat.Presheaf.IsFlasque
      ((Opens.grothendieckTopology X).plusObj
        (singularCochainPresheaf R X n)) where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro y
    obtain ⟨φV, hφV⟩ := singularCochain_toPlus_exists_rep R X V.unop n y
    obtain ⟨φU, hφU⟩ := openSingularCochainRestriction_surjective R X i n φV
    refine ⟨((Opens.grothendieckTopology X).toPlus
      (singularCochainPresheaf R X n)).app U φU, ?_⟩
    rw [← ConcreteCategory.comp_apply,
      ← ((Opens.grothendieckTopology X).toPlus
        (singularCochainPresheaf R X n)).naturality i,
      ConcreteCategory.comp_apply, hφU, hφV]

abbrev ZeroSimplex (U : (Opens X)ᵒᵖ) := OpenSimplex X U 0

/-- The degree-zero singular chain associated to a point of an open subset. -/
noncomputable def singularZeroChainOfPoint (U : (Opens X)ᵒᵖ) (x : U.unop) :
    OpenChains R X U 0 :=
  singularChainOfSimplex R X U 0
    ((@TopCat.toSSetObj₀Equiv.{u} ((Opens.toTopCat X).obj U.unop)).symm x)

/-- The zero-chain associated to a point is natural under inclusion of open subsets. -/
lemma singularZeroChainOfPoint_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (x : V.unop) :
    (((openSingularChainComplexFunctor R X).map i.unop).f 0).hom
        (singularZeroChainOfPoint R X V x) =
      singularZeroChainOfPoint R X U (i.unop x) := by
  let f := TopCat.toSSet.map ((Opens.toTopCat X).map i.unop)
  let s := (@TopCat.toSSetObj₀Equiv.{u} ((Opens.toTopCat X).obj V.unop)).symm x
  have hs := SSet.ι_chainComplexMap_f _ _ f (ModuleCat.of R R) s
  exact congrArg (fun g ↦ g.hom 1) hs

/-- Evaluate a degree-zero singular cochain on the chain associated to each point. -/
def singularZeroCochainToFunction (U : (Opens X)ᵒᵖ) :
    OpenCochains R X U 0 →ₗ[R] (U.unop → R) where
  toFun φ x := singularCochainToSimplexFunction R X U 0 φ
    ((@TopCat.toSSetObj₀Equiv.{u} ((Opens.toTopCat X).obj U.unop)).symm x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation of zero-cochains commutes with restriction to an open subset. -/
lemma singularZeroCochainToFunction_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (φ : OpenCochains R X U 0) :
    singularZeroCochainToFunction R X V ((singularCochainPresheaf R X 0).map i φ) =
      fun x ↦ singularZeroCochainToFunction R X U φ (i.unop x) := by
  ext x
  change φ ((((openSingularChainComplexFunctor R X).map i.unop).f 0).hom
    (singularZeroChainOfPoint R X V x)) =
    φ (singularZeroChainOfPoint R X U (i.unop x))
  rw [singularZeroChainOfPoint_naturality]

/-- Construct a degree-zero singular cochain by transporting a function on points along the
canonical equivalence between points and singular zero-simplices. -/
noncomputable def singularZeroCochainOfFunction (U : (Opens X)ᵒᵖ) :
    (U.unop → R) →ₗ[R] OpenCochains R X U 0 where
  toFun f := singularCochainOfSimplexFunction R X U 0
    (f ∘ (@TopCat.toSSetObj₀Equiv.{u} ((Opens.toTopCat X).obj U.unop)))
  map_add' f g := by
    rw [← map_add]
    rfl
  map_smul' a f := by
    rw [← map_smul]
    rfl

@[simp]
lemma singularZeroCochainToFunction_ofFunction (U : (Opens X)ᵒᵖ) (f : U.unop → R) :
    singularZeroCochainToFunction R X U (singularZeroCochainOfFunction R X U f) = f := by
  ext x
  change singularCochainToSimplexFunction R X U 0
      (singularCochainOfSimplexFunction R X U 0
        (f ∘ (@TopCat.toSSetObj₀Equiv.{u} ((Opens.toTopCat X).obj U.unop))))
      ((@TopCat.toSSetObj₀Equiv.{u} ((Opens.toTopCat X).obj U.unop)).symm x) = f x
  rw [congrFun (singularCochainToSimplexFunction_ofFunction R X U 0 _) _]
  exact congrArg f
    ((@TopCat.toSSetObj₀Equiv.{u} ((Opens.toTopCat X).obj U.unop)).apply_symm_apply x)

@[simp]
lemma singularZeroCochainOfFunction_toFunction (U : (Opens X)ᵒᵖ)
    (φ : OpenCochains R X U 0) :
    singularZeroCochainOfFunction R X U (singularZeroCochainToFunction R X U φ) = φ := by
  change singularCochainOfSimplexFunction R X U 0
      ((singularZeroCochainToFunction R X U φ) ∘
        (@TopCat.toSSetObj₀Equiv.{u} ((Opens.toTopCat X).obj U.unop))) = φ
  have hfun :
      (singularZeroCochainToFunction R X U φ) ∘
          (@TopCat.toSSetObj₀Equiv.{u} ((Opens.toTopCat X).obj U.unop)) =
        singularCochainToSimplexFunction R X U 0 φ := by
    ext s
    change singularCochainToSimplexFunction R X U 0 φ
      ((@TopCat.toSSetObj₀Equiv.{u} ((Opens.toTopCat X).obj U.unop)).symm
        ((@TopCat.toSSetObj₀Equiv.{u} ((Opens.toTopCat X).obj U.unop)) s)) = _
    rw [Equiv.symm_apply_apply]
  rw [hfun, singularCochainOfSimplexFunction_toFunction]

/-- Degree-zero singular cochains are the all-degree simplex-function equivalence specialized at
zero, transported along Mathlib's equivalence between zero-simplices and points. -/
noncomputable def singularZeroCochainEquivFunction (U : (Opens X)ᵒᵖ) :
    OpenCochains R X U 0 ≃ₗ[R] (U.unop → R) := by
  refine LinearEquiv.ofLinearMap (singularZeroCochainToFunction R X U)
    (singularZeroCochainOfFunction R X U) ?_ ?_
  · ext f x
    exact congrFun (singularZeroCochainToFunction_ofFunction R X U f) x
  · ext φ c
    exact congrArg (fun f ↦ f c) (singularZeroCochainOfFunction_toFunction R X U φ)

/-- Restriction of arbitrary functions along an inclusion of open subsets. -/
def openFunctionRestriction {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (U.unop → R) →ₗ[R] (V.unop → R) where
  toFun f := f ∘ i.unop
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The additive presheaf of arbitrary `R`-valued functions. -/
def functionPresheaf : TopCat.Presheaf AddCommGrpCat X where
  obj U := AddCommGrpCat.of (U.unop → R)
  map i := AddCommGrpCat.ofHom (openFunctionRestriction R X i).toAddMonoidHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The degree-zero singular-cochain presheaf is the presheaf of arbitrary functions. -/
noncomputable def singularZeroCochainPresheafIsoFunction :
    singularCochainPresheaf R X 0 ≅ functionPresheaf R X :=
  NatIso.ofComponents
    (fun U ↦ (singularZeroCochainEquivFunction R X U).toAddEquiv.toAddCommGrpIso)
    (fun i ↦ by
      ext φ
      funext x
      exact congrFun (singularZeroCochainToFunction_naturality R X i φ) x)

/-- Arbitrary `R`-valued functions form an additive sheaf. -/
lemma functionPresheaf_isSheaf :
    TopCat.Presheaf.IsSheaf (functionPresheaf R X) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (forget AddCommGrpCat)]
  exact TopCat.Presheaf.toType_isSheaf X R

/-- The degree-zero singular-cochain presheaf is already a sheaf. -/
lemma singularCochainPresheaf_zero_isSheaf :
    TopCat.Presheaf.IsSheaf (singularCochainPresheaf R X 0) :=
  (TopCat.Presheaf.isSheaf_iso_iff
    (singularZeroCochainPresheafIsoFunction R X)).mpr
      (functionPresheaf_isSheaf R X)

/-- Sheafification does not change the degree-zero singular-cochain presheaf. -/
noncomputable instance singularCochainPresheaf_zero_toSheafify_isIso :
    IsIso (toSheafify (Opens.grothendieckTopology X)
      (singularCochainPresheaf R X 0)) :=
  CategoryTheory.isIso_toSheafify (Opens.grothendieckTopology X)
    (singularCochainPresheaf_zero_isSheaf R X)

/-- The degree-zero singular-cochain sheaf is flasque. -/
instance singularCochainSheaf_zero_isFlasque :
    TopCat.Sheaf.IsFlasque (singularCochainSheaf R X 0) where
  epi {U V} i := by
    let J := Opens.grothendieckTopology X
    let P := singularCochainPresheaf R X 0
    let η := toSheafify J P
    let : IsIso η := singularCochainPresheaf_zero_toSheafify_isIso R X
    change Epi ((CategoryTheory.sheafify J P).map i)
    have hcomp : Epi (η.app U ≫ (CategoryTheory.sheafify J P).map i) := by
      rw [← η.naturality i]
      infer_instance
    exact CategoryTheory.epi_of_epi (η.app U)
      ((CategoryTheory.sheafify J P).map i)

end AlgebraicTopology.Singular
