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

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Sheaves.Abelian

import FormalConjecturesForMathlib.Mathlib.Algebra.Homology.DualExact
import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularContractible
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy
import Mathlib.Topology.Sheaves.Sheafify

/-!
# The singular-cochain sheaf

This file constructs the singular cochain presheaf on a topological space. In degree `n`, its
sections over an open set `U` are the linear dual of the singular `n`-chains of `U`. Restriction is
dual to the chain map induced by an inclusion of open sets. The singular boundary dualizes to the
coboundary, giving a cochain complex. Degreewise sheafification gives the singular-cochain sheaf
complex.

These constructions are prerequisites for comparing singular cohomology with constant-sheaf
cohomology. The comparison is proved in degree zero on locally path-connected spaces. In positive
degrees, an explicit neighborhood-wise primitive condition is shown to imply the comparison.
No local acyclicity statement is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopCat.{u})

/-- The singular chain complex, functorially restricted to the open subsets of `X`. -/
def openSingularChainComplexFunctor :
    Opens X ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  Opens.toTopCat X ⋙
    (singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)

/-- Singular chains of an open subset of `X` in degree `n`. -/
abbrev OpenChains (U : (Opens X)ᵒᵖ) (n : ℕ) :=
  (openSingularChainComplexFunctor R X).obj U.unop |>.X n

/-- Singular cochains of an open subset of `X` in degree `n`. -/
abbrev OpenCochains (U : (Opens X)ᵒᵖ) (n : ℕ) :=
  Module.Dual R (OpenChains R X U n)

/-- The singular cochain presheaf in a fixed degree. -/
def singularCochainPresheaf (n : ℕ) : TopCat.Presheaf AddCommGrpCat X where
  obj U := AddCommGrpCat.of (OpenCochains R X U n)
  map {U V} i := AddCommGrpCat.ofHom <|
    (((openSingularChainComplexFunctor R X).map i.unop).f n).hom.dualMap.toAddMonoidHom
  map_id U := by
    change AddCommGrpCat.ofHom
        (((((openSingularChainComplexFunctor R X).map (𝟙 U.unop)).f n).hom.dualMap)
          |>.toAddMonoidHom) = 𝟙 _
    rw [(openSingularChainComplexFunctor R X).map_id]
    rfl
  map_comp {U V W} i j := by
    rw [show (i ≫ j).unop = j.unop ≫ i.unop by rfl,
      (openSingularChainComplexFunctor R X).map_comp]
    rfl

/-- The singular coboundary, dual to the singular boundary. -/
def singularCochainCoboundary (n : ℕ) :
    singularCochainPresheaf R X n ⟶ singularCochainPresheaf R X (n + 1) where
  app U := AddCommGrpCat.ofHom <|
    ((((openSingularChainComplexFunctor R X).obj U.unop).d
      (n + 1) n).hom.dualMap).toAddMonoidHom
  naturality {U V} i := by
    ext φ
    change OpenCochains R X U n at φ
    apply LinearMap.ext
    intro c
    change φ
        (((((openSingularChainComplexFunctor R X).map i.unop).f n).hom)
          (((openSingularChainComplexFunctor R X).obj V.unop).d (n + 1) n |>.hom c)) =
      φ
        ((((openSingularChainComplexFunctor R X).obj U.unop).d (n + 1) n |>.hom)
          (((openSingularChainComplexFunctor R X).map i.unop).f (n + 1) |>.hom c))
    calc
      _ = φ (ModuleCat.Hom.hom
          (((openSingularChainComplexFunctor R X).obj V.unop).d (n + 1) n ≫
            ((openSingularChainComplexFunctor R X).map i.unop).f n) c) := rfl
      _ = φ (ModuleCat.Hom.hom
          (((openSingularChainComplexFunctor R X).map i.unop).f (n + 1) ≫
            ((openSingularChainComplexFunctor R X).obj U.unop).d (n + 1) n) c) :=
        congrArg (fun f ↦ φ (ModuleCat.Hom.hom f c))
          (((openSingularChainComplexFunctor R X).map i.unop).comm (n + 1) n).symm
      _ = _ := rfl

/-- Consecutive singular coboundaries compose to zero. -/
lemma singularCochainCoboundary_comp (n : ℕ) :
    singularCochainCoboundary R X n ≫ singularCochainCoboundary R X (n + 1) = 0 := by
  apply NatTrans.ext
  funext U
  ext φ
  change OpenCochains R X U n at φ
  apply LinearMap.ext
  intro c
  let K := (openSingularChainComplexFunctor R X).obj U.unop
  change φ ((K.d (n + 1) n).hom ((K.d (n + 2) (n + 1)).hom c)) = 0
  have h := K.d_comp_d (n + 2) (n + 1) n
  calc
    _ = φ (ModuleCat.Hom.hom
        (K.d (n + 2) (n + 1) ≫ K.d (n + 1) n) c) := rfl
    _ = φ (ModuleCat.Hom.hom (0 : K.X (n + 2) ⟶ K.X n) c) :=
      congrArg (fun f ↦ φ (ModuleCat.Hom.hom f c)) h
    _ = φ 0 := rfl
    _ = 0 := φ.map_zero

/-- The singular cochain complex as a complex of presheaves. -/
def singularCochainPresheafComplex :
    CochainComplex (TopCat.Presheaf AddCommGrpCat X) ℕ :=
  CochainComplex.of
    (singularCochainPresheaf R X)
    (singularCochainCoboundary R X)
    (singularCochainCoboundary_comp R X)

@[simp]
lemma singularCochainPresheafComplex_d (n : ℕ) :
    (singularCochainPresheafComplex R X).d n (n + 1) =
      singularCochainCoboundary R X n := by
  simp [singularCochainPresheafComplex]

/-- Singular cochains in a fixed degree, sheafified as additive groups. -/
def singularCochainSheaf (n : ℕ) : TopCat.Sheaf AddCommGrpCat X :=
  let J := Opens.grothendieckTopology X
  (presheafToSheaf J AddCommGrpCat).obj (singularCochainPresheaf R X n)

/-- The sheafified singular coboundary. -/
def singularCochainSheafCoboundary (n : ℕ) :
    singularCochainSheaf R X n ⟶ singularCochainSheaf R X (n + 1) :=
  let J := Opens.grothendieckTopology X
  (presheafToSheaf J AddCommGrpCat).map (singularCochainCoboundary R X n)

/-- The degreewise sheafification of the singular cochain complex. -/
def singularCochainSheafComplex :
    CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℕ :=
  let J := Opens.grothendieckTopology X
  ((presheafToSheaf J AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (singularCochainPresheafComplex R X)

@[simp]
lemma singularCochainSheafComplex_d (n : ℕ) :
    (singularCochainSheafComplex R X).d n (n + 1) =
      singularCochainSheafCoboundary R X n := by
  change (presheafToSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat).map
        ((singularCochainPresheafComplex R X).d n (n + 1)) = _
  rw [singularCochainPresheafComplex_d]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The degreewise sheafification unit from singular cochains to the underlying presheaf of the
singular-cochain sheaf complex. -/
noncomputable def singularCochainSheafificationUnit :
    singularCochainPresheafComplex R X ⟶
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X).mapHomologicalComplex
        (ComplexShape.up ℕ) |>.obj (singularCochainSheafComplex R X) where
  f n := toSheafify (Opens.grothendieckTopology X)
    (singularCochainPresheaf R X n)
  comm' i j hij := by
    obtain rfl := hij
    rw [Functor.mapHomologicalComplex_obj_d, singularCochainPresheafComplex_d,
      singularCochainSheafComplex_d]
    dsimp [singularCochainSheafCoboundary, singularCochainSheaf]
    exact (toSheafify_naturality (Opens.grothendieckTopology X)
      (singularCochainCoboundary R X i)).symm

/-- The augmentation of simplicial zero-chains, sending every vertex to `1`. -/
def simplicialZeroAugmentation (S : SSet.{u}) :
    (S.chainComplex (ModuleCat.of R R)).X 0 ⟶ ModuleCat.of R R :=
  Limits.Sigma.desc (fun _ ↦ 𝟙 _)

@[reassoc (attr := simp)]
lemma ιChainComplex_comp_simplicialZeroAugmentation (S : SSet.{u})
    (σ : S.obj (.op ⟨0⟩)) :
    S.ιChainComplex σ ≫ simplicialZeroAugmentation R S = 𝟙 _ :=
  Limits.Sigma.ι_desc (fun _ ↦ 𝟙 (ModuleCat.of R R)) σ

/-- The zero-chain augmentation is natural in the simplicial set. -/
lemma simplicialZeroAugmentation_naturality {S T : SSet.{u}} (f : S ⟶ T) :
    (SSet.chainComplexMap f (ModuleCat.of R R)).f 0 ≫
      simplicialZeroAugmentation R T = simplicialZeroAugmentation R S := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f,
    ιChainComplex_comp_simplicialZeroAugmentation,
    ιChainComplex_comp_simplicialZeroAugmentation]

/-- The simplicial boundary of a one-chain has augmentation zero. -/
private lemma simplicialBoundary_comp_zeroAugmentation (S : SSet.{u}) :
    (S.chainComplex (ModuleCat.of R R)).d 1 0 ≫
      simplicialZeroAugmentation R S = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, ιChainComplex_comp_simplicialZeroAugmentation]
  simp

/-- The augmentation on the zero-chains of an open subset. -/
def openZeroAugmentation (U : (Opens X)ᵒᵖ) :
    OpenChains R X U 0 ⟶ ModuleCat.of R R :=
  simplicialZeroAugmentation R <|
    TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop)

/-- Restriction of open subsets commutes with the zero-chain augmentation. -/
lemma openZeroAugmentation_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    ((openSingularChainComplexFunctor R X).map i.unop).f 0 ≫
      openZeroAugmentation R X U = openZeroAugmentation R X V :=
  simplicialZeroAugmentation_naturality R
    (TopCat.toSSet.map ((Opens.toTopCat X).map i.unop))

/-- The boundary of an open singular one-chain has augmentation zero. -/
private lemma openBoundary_comp_zeroAugmentation (U : (Opens X)ᵒᵖ) :
    ((openSingularChainComplexFunctor R X).obj U.unop).d 1 0 ≫
      openZeroAugmentation R X U = 0 :=
  simplicialBoundary_comp_zeroAugmentation R
    (TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop))

/-- The constant presheaf with value the additive group of `R`. -/
def constantCoefficientPresheaf : TopCat.Presheaf AddCommGrpCat X :=
  (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of R)

/-- A scalar defines the corresponding constant singular zero-cochain. -/
def constantSingularZeroCochain (U : (Opens X)ᵒᵖ) :
    R →+ OpenCochains R X U 0 where
  toFun r := r • (openZeroAugmentation R X U).hom
  map_zero' := LinearMap.ext fun c ↦ by simp
  map_add' r s := LinearMap.ext fun c ↦ by simp [add_smul]

/-- Constant functions form singular zero-cochains, naturally under restriction. -/
def constantsToSingularCochainZero :
    constantCoefficientPresheaf R X ⟶ singularCochainPresheaf R X 0 where
  app U := AddCommGrpCat.ofHom (constantSingularZeroCochain R X U)
  naturality {U V} i := by
    ext r
    change R at r
    apply LinearMap.ext
    intro c
    dsimp [constantCoefficientPresheaf, constantSingularZeroCochain,
      singularCochainPresheaf]
    exact congrArg (r * ·) <| congrArg (fun f ↦ f.hom c) <|
      (openZeroAugmentation_naturality R X i).symm

/-- Constant zero-cochains have zero coboundary. -/
lemma constantsToSingularCochainZero_comp_coboundary :
    constantsToSingularCochainZero R X ≫ singularCochainCoboundary R X 0 = 0 := by
  apply NatTrans.ext
  funext U
  ext r
  change R at r
  apply LinearMap.ext
  intro c
  dsimp [constantsToSingularCochainZero, constantSingularZeroCochain,
    constantCoefficientPresheaf, singularCochainPresheaf, singularCochainCoboundary]
  change r * (openZeroAugmentation R X U).hom
      ((((openSingularChainComplexFunctor R X).obj U.unop).d 1 0).hom c) = 0
  have hc : (openZeroAugmentation R X U).hom
      ((((openSingularChainComplexFunctor R X).obj U.unop).d 1 0).hom c) = 0 := by
    calc
      _ = ModuleCat.Hom.hom
          (((openSingularChainComplexFunctor R X).obj U.unop).d 1 0 ≫
            openZeroAugmentation R X U) c := rfl
      _ = ModuleCat.Hom.hom
          (0 : OpenChains R X U 1 ⟶ ModuleCat.of R R) c :=
        congrArg (fun f ↦ f.hom c) (openBoundary_comp_zeroAugmentation R X U)
      _ = 0 := rfl
  rw [hc, mul_zero]

/-- The canonical augmentation from the constant presheaf complex to singular cochains. -/
def constantsToSingularCochainPresheafComplex :
    (CochainComplex.single₀ (TopCat.Presheaf AddCommGrpCat X)).obj
        (constantCoefficientPresheaf R X) ⟶ singularCochainPresheafComplex R X :=
  HomologicalComplex.mkHomFromSingle (constantsToSingularCochainZero R X) <| by
    intro k hk
    obtain rfl : k = 1 := by simpa using hk.symm
    change constantsToSingularCochainZero R X ≫
      (singularCochainPresheafComplex R X).d 0 1 = 0
    rw [singularCochainPresheafComplex_d]
    exact constantsToSingularCochainZero_comp_coboundary R X

/-- The constant sheaf with value the additive group of `R`. -/
def constantCoefficientSheaf : TopCat.Sheaf AddCommGrpCat X :=
  let J := Opens.grothendieckTopology X
  (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of R)

/-- The sheafified inclusion of constants into singular zero-cochains. -/
def constantsToSingularCochainZeroSheaf :
    constantCoefficientSheaf R X ⟶ singularCochainSheaf R X 0 :=
  let J := Opens.grothendieckTopology X
  (presheafToSheaf J AddCommGrpCat).map (constantsToSingularCochainZero R X)

/-- Constant sections have zero sheafified singular coboundary. -/
lemma constantsToSingularCochainZeroSheaf_comp_coboundary :
    constantsToSingularCochainZeroSheaf R X ≫
      singularCochainSheafCoboundary R X 0 = 0 := by
  let J := Opens.grothendieckTopology X
  change (presheafToSheaf J AddCommGrpCat).map
      (constantsToSingularCochainZero R X) ≫
    (presheafToSheaf J AddCommGrpCat).map
      (singularCochainCoboundary R X 0) = 0
  rw [← Functor.map_comp, constantsToSingularCochainZero_comp_coboundary,
    Functor.map_zero]

/-- The augmented singular zero-cochain short complex before sheafification. -/
noncomputable def constantsToSingularCochainPresheafShortComplex :
    ShortComplex (TopCat.Presheaf AddCommGrpCat X) :=
  ShortComplex.mk (constantsToSingularCochainZero R X)
    (singularCochainCoboundary R X 0)
    (constantsToSingularCochainZero_comp_coboundary R X)

/-- The augmented singular zero-cochain short complex after sheafification. -/
noncomputable def constantsToSingularCochainSheafShortComplex :
    ShortComplex (TopCat.Sheaf AddCommGrpCat X) :=
  ShortComplex.mk (constantsToSingularCochainZeroSheaf R X)
    (singularCochainSheafCoboundary R X 0)
    (constantsToSingularCochainZeroSheaf_comp_coboundary R X)

set_option backward.isDefEq.respectTransparency false in
/-- The sheafification unit between the augmented presheaf and sheaf short complexes. -/
noncomputable def constantsToSingularCochainShortComplexSheafificationUnit :
    constantsToSingularCochainPresheafShortComplex R X ⟶
      (constantsToSingularCochainSheafShortComplex R X).map
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X) where
  τ₁ := toSheafify (Opens.grothendieckTopology X) (constantCoefficientPresheaf R X)
  τ₂ := toSheafify (Opens.grothendieckTopology X) (singularCochainPresheaf R X 0)
  τ₃ := toSheafify (Opens.grothendieckTopology X) (singularCochainPresheaf R X 1)
  comm₁₂ := (toSheafify_naturality (Opens.grothendieckTopology X)
    (constantsToSingularCochainZero R X)).symm
  comm₂₃ := (toSheafify_naturality (Opens.grothendieckTopology X)
    (singularCochainCoboundary R X 0)).symm

/-- The canonical comparison from the constant sheaf complex to the singular-cochain sheaf
complex. -/
def constantsToSingularCochainSheafComplex :
    (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat X)).obj
        (constantCoefficientSheaf R X) ⟶ singularCochainSheafComplex R X :=
  (CochainComplex.fromSingle₀Equiv (singularCochainSheafComplex R X)
    (constantCoefficientSheaf R X)).symm
      ⟨constantsToSingularCochainZeroSheaf R X, by
        rw [singularCochainSheafComplex_d]
        exact constantsToSingularCochainZeroSheaf_comp_coboundary R X⟩

end AlgebraicTopology.Singular
