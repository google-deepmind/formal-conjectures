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

import FormalConjecturesForMathlib.Algebra.Homology.DualExact
import FormalConjecturesForMathlib.AlgebraicTopology.SingularContractible
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

/-- A neighborhood-wise lifting of every local kernel section gives exactness after passing to
the stalk. The lift may be taken after shrinking the original neighborhood. -/
lemma stalkExact_of_locallyPrimitive
    (S : ShortComplex (TopCat.Presheaf AddCommGrpCat.{u} X))
    (hlocal : ∀ (x : X) (U : Opens X) (_hx : x ∈ U)
      (s : S.X₂.obj (.op U)), S.g.app (.op U) s = 0 →
        ∃ (V : Opens X) (_hxV : x ∈ V) (i : V ⟶ U) (t : S.X₁.obj (.op V)),
          S.f.app (.op V) t = S.X₂.map i.op s)
    (x : X) :
    (S.map (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro z hz
  obtain ⟨U, hxU, s, rfl⟩ := S.X₂.exists_germ_eq z
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g
      (S.X₂.germ U x hxU s) = 0 at hz
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hz
  have hz' : S.X₃.germ U x hxU (S.g.app (.op U) s) =
      S.X₃.germ U x hxU 0 := by
    rw [map_zero]
    exact hz
  obtain ⟨W, hxW, iWU, iWU', hW⟩ :=
    S.X₃.germ_eq x hxU hxU (S.g.app (.op U) s) 0 hz'
  have hWs : S.g.app (.op W) (S.X₂.map iWU.op s) = 0 := by
    rw [← ConcreteCategory.comp_apply, S.g.naturality, ConcreteCategory.comp_apply]
    simpa using hW
  obtain ⟨V, hxV, iVW, t, ht⟩ :=
    hlocal x W hxW (S.X₂.map iWU.op s) hWs
  refine ⟨S.X₁.germ V x hxV t, ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.f
      (S.X₁.germ V x hxV t) = S.X₂.germ U x hxU s
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht,
    S.X₂.germ_res_apply iVW x hxV, S.X₂.germ_res_apply iWU x hxW]

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

set_option backward.isDefEq.respectTransparency false in
/-- If every closed singular `(n + 1)`-cochain has a primitive near each point, then the
sheafified singular-cochain complex is exact in degree `n + 1`. The hypothesis explicitly gives
the primitive after restricting to a smaller neighborhood. -/
lemma singularCochainSheafComplex_exactAt_succ_of_locallyPrimitive (n : ℕ)
    (hlocal : ∀ (x : X) (U : Opens X) (_hx : x ∈ U)
      (φ : OpenCochains R X (.op U) (n + 1)),
        (singularCochainCoboundary R X (n + 1)).app (.op U) φ = 0 →
        ∃ (V : Opens X) (_hxV : x ∈ V) (i : V ⟶ U)
          (ψ : OpenCochains R X (.op V) n),
          (singularCochainCoboundary R X n).app (.op V) ψ =
            (singularCochainPresheaf R X (n + 1)).map i.op φ) :
    (singularCochainSheafComplex R X).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff'
    (K := singularCochainSheafComplex R X)
    (i := n) (j := n + 1) (k := (n + 1) + 1) (by simp) (by simp)]
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  let stalk := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let P := singularCochainPresheafComplex R X
  have hP : (P.sc' n (n + 1) ((n + 1) + 1)).map stalk |>.Exact :=
    stalkExact_of_locallyPrimitive X (P.sc' n (n + 1) ((n + 1) + 1)) (by
      intro y U hyU φ hφ
      dsimp [P, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor'] at hφ ⊢
      rw [singularCochainPresheafComplex_d] at hφ
      rw [singularCochainPresheafComplex_d]
      change (singularCochainCoboundary R X (n + 1)).app (.op U) φ = 0 at hφ
      exact hlocal y U hyU φ hφ) x
  let unit := singularCochainSheafificationUnit R X
  let stalkUnit := (stalk.mapHomologicalComplex (ComplexShape.up ℕ)).map unit
  let η := (HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{u}
    (ComplexShape.up ℕ) n (n + 1) ((n + 1) + 1)).map stalkUnit
  let : IsIso η.τ₁ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
      (singularCochainPresheaf R X n)
  let : IsIso η.τ₂ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
      (singularCochainPresheaf R X (n + 1))
  let : IsIso η.τ₃ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
      (singularCochainPresheaf R X ((n + 1) + 1))
  let : IsIso η := ShortComplex.isIso_of_isIso η
  exact ShortComplex.exact_of_iso (asIso η) hP

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
lemma simplicialBoundary_comp_zeroAugmentation (S : SSet.{u}) :
    (S.chainComplex (ModuleCat.of R R)).d 1 0 ≫
      simplicialZeroAugmentation R S = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, ιChainComplex_comp_simplicialZeroAugmentation]
  simp

/-- Scaling the zero-chain augmentation is injective when the simplicial set has a vertex. -/
lemma smul_simplicialZeroAugmentation_injective (S : SSet.{u})
    [Nonempty (S.obj (.op ⟨0⟩))] :
    Function.Injective (fun r : R ↦ r • (simplicialZeroAugmentation R S).hom) := by
  intro r s h
  let x : S.obj (.op ⟨0⟩) := Classical.arbitrary _
  have heval : (simplicialZeroAugmentation R S).hom
      ((S.ιChainComplex (R := ModuleCat.of R R) x).hom 1) = 1 :=
    congrArg (fun f ↦ f.hom 1)
      (ιChainComplex_comp_simplicialZeroAugmentation R S x)
  have hvalue := LinearMap.congr_fun h
    ((S.ιChainComplex (R := ModuleCat.of R R) x).hom 1)
  simpa [heval] using hvalue

/-- On a connected simplicial set, every singular zero-cocycle is constant. This is exactness of
the augmented singular cochain complex in degree zero. -/
lemma exists_eq_smul_simplicialZeroAugmentation_of_connected (S : SSet.{u}) [S.IsConnected]
    (φ : Module.Dual R ((S.chainComplex (ModuleCat.of R R)).X 0))
    (hφ : ((S.chainComplex (ModuleCat.of R R)).d 1 0).hom.dualMap φ = 0) :
    ∃ r : R, r • (simplicialZeroAugmentation R S).hom = φ := by
  have hd : (S.chainComplex (ModuleCat.of R R)).d 1 0 ≫ ModuleCat.ofHom φ = 0 :=
    ModuleCat.hom_ext (LinearMap.ext (LinearMap.congr_fun hφ))
  let s := CokernelCofork.ofπ (ModuleCat.ofHom φ) hd
  let q := SSet.π₀.fromChainComplexXZero S (ModuleCat.of R R)
  let g := (S.isColimitCokernelCoforkChainComplexDOneZero
    (ModuleCat.of R R)).desc s
  have hfac : q ≫ g = ModuleCat.ofHom φ :=
    (S.isColimitCokernelCoforkChainComplexDOneZero
      (ModuleCat.of R R)).fac s WalkingParallelPair.one
  let x₀ : S.obj (.op ⟨0⟩) := Classical.arbitrary _
  let r : R := φ ((S.ιChainComplex (R := ModuleCat.of R R) x₀).hom 1)
  refine ⟨r, ?_⟩
  apply LinearMap.ext
  intro c
  have heq : ModuleCat.ofHom (r • (simplicialZeroAugmentation R S).hom) =
      ModuleCat.ofHom φ := by
    apply SSet.chainComplex_hom_ext
    intro x
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    have hx : SSet.π₀.mk x = SSet.π₀.mk x₀ := Subsingleton.elim _ _
    have hvertexMap :
        S.ιChainComplex (R := ModuleCat.of R R) x ≫ ModuleCat.ofHom φ =
          S.ιChainComplex (R := ModuleCat.of R R) x₀ ≫ ModuleCat.ofHom φ := by
      calc
        _ = S.ιChainComplex (R := ModuleCat.of R R) x ≫ (q ≫ g) :=
          congrArg (fun k ↦ S.ιChainComplex (R := ModuleCat.of R R) x ≫ k) hfac.symm
        _ = (S.ιChainComplex (R := ModuleCat.of R R) x ≫ q) ≫ g :=
          Category.assoc _ _ _ |>.symm
        _ = Limits.Sigma.ι (fun _ : SSet.π₀ S ↦ ModuleCat.of R R)
              (SSet.π₀.mk x) ≫ g := by
          rw [show q = SSet.π₀.fromChainComplexXZero S (ModuleCat.of R R) by rfl,
            SSet.π₀.comp_fromChainComplexXZero]
        _ = Limits.Sigma.ι (fun _ : SSet.π₀ S ↦ ModuleCat.of R R)
              (SSet.π₀.mk x₀) ≫ g := by rw [hx]
        _ = (S.ιChainComplex (R := ModuleCat.of R R) x₀ ≫ q) ≫ g := by
          rw [show q = SSet.π₀.fromChainComplexXZero S (ModuleCat.of R R) by rfl,
            SSet.π₀.comp_fromChainComplexXZero]
        _ = S.ιChainComplex (R := ModuleCat.of R R) x₀ ≫ (q ≫ g) :=
          Category.assoc _ _ _
        _ = _ := congrArg
          (fun k ↦ S.ιChainComplex (R := ModuleCat.of R R) x₀ ≫ k) hfac
    have hvalue : φ ((S.ιChainComplex (R := ModuleCat.of R R) x).hom t) =
        φ ((S.ιChainComplex (R := ModuleCat.of R R) x₀).hom t) :=
      congrArg (fun f ↦ f.hom t) hvertexMap
    have hscale : φ ((S.ιChainComplex (R := ModuleCat.of R R) x₀).hom t) =
        t * r := by
      dsimp [r]
      conv_lhs =>
        rw [show t = t • (1 : R) by simp, map_smul, map_smul, smul_eq_mul]
    calc
      _ = r * t := by
        change r * (simplicialZeroAugmentation R S).hom
          ((S.ιChainComplex (R := ModuleCat.of R R) x).hom t) = r * t
        rw [show (simplicialZeroAugmentation R S).hom
            ((S.ιChainComplex (R := ModuleCat.of R R) x).hom t) = t by
          exact congrArg (fun f ↦ f.hom t)
            (ιChainComplex_comp_simplicialZeroAugmentation R S x)]
      _ = t * r := mul_comm _ _
      _ = φ ((S.ιChainComplex (R := ModuleCat.of R R) x₀).hom t) := hscale.symm
      _ = φ ((S.ιChainComplex (R := ModuleCat.of R R) x).hom t) := hvalue.symm
  exact congrArg (fun f ↦ f.hom c) heq

/-- On a connected simplicial set, every singular zero-cocycle is represented by a unique
constant. -/
lemma existsUnique_eq_smul_simplicialZeroAugmentation_of_connected
    (S : SSet.{u}) [S.IsConnected]
    (φ : Module.Dual R ((S.chainComplex (ModuleCat.of R R)).X 0))
    (hφ : ((S.chainComplex (ModuleCat.of R R)).d 1 0).hom.dualMap φ = 0) :
    ∃! r : R, r • (simplicialZeroAugmentation R S).hom = φ := by
  obtain ⟨r, hr⟩ := exists_eq_smul_simplicialZeroAugmentation_of_connected R S φ hφ
  exact ⟨r, hr, fun s hs ↦
    smul_simplicialZeroAugmentation_injective R S (hs.trans hr.symm)⟩

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
lemma openBoundary_comp_zeroAugmentation (U : (Opens X)ᵒᵖ) :
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

/-- Constant singular zero-cochains on a nonempty open set have unique coefficients. -/
lemma constantSingularZeroCochain_injective (U : (Opens X)ᵒᵖ) [Nonempty U.unop] :
    Function.Injective (constantSingularZeroCochain R X U) := by
  let : Nonempty
      ((TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop)).obj (.op ⟨0⟩)) :=
    ⟨(TopCat.toSSetObj₀Equiv (X := (Opens.toTopCat X).obj U.unop)).symm
      (Classical.arbitrary U.unop)⟩
  exact smul_simplicialZeroAugmentation_injective R
    (TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop))

/-- On a path-connected open subset, every singular zero-cocycle is a constant cochain. -/
lemma exists_eq_constantSingularZeroCochain_of_pathConnected (U : (Opens X)ᵒᵖ)
    [PathConnectedSpace U.unop]
    (φ : OpenCochains R X U 0)
    (hφ : (((openSingularChainComplexFunctor R X).obj U.unop).d 1 0).hom.dualMap φ = 0) :
    ∃ r : R, constantSingularZeroCochain R X U r = φ := by
  let : PathConnectedSpace ((Opens.toTopCat X).obj U.unop) :=
    show PathConnectedSpace U.unop from inferInstance
  exact exists_eq_smul_simplicialZeroAugmentation_of_connected R
    (TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop)) φ hφ

/-- On a path-connected open subset, every singular zero-cocycle is represented by a unique
constant. -/
lemma existsUnique_eq_constantSingularZeroCochain_of_pathConnected (U : (Opens X)ᵒᵖ)
    [PathConnectedSpace U.unop]
    (φ : OpenCochains R X U 0)
    (hφ : (((openSingularChainComplexFunctor R X).obj U.unop).d 1 0).hom.dualMap φ = 0) :
    ∃! r : R, constantSingularZeroCochain R X U r = φ := by
  let : PathConnectedSpace ((Opens.toTopCat X).obj U.unop) :=
    show PathConnectedSpace U.unop from inferInstance
  exact existsUnique_eq_smul_simplicialZeroAugmentation_of_connected R
    (TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop)) φ hφ

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

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of constant zero-cochains is a monomorphism on every stalk. The raw constant
presheaf need not be a monomorphism on the empty open set, but that does not affect stalks. -/
lemma constantsToSingularCochainZero_stalk_mono (x : X) :
    Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (constantsToSingularCochainZero R X)) := by
  rw [AddCommGrpCat.mono_iff_injective]
  intro z z' h
  obtain ⟨U, hxU, r, rfl⟩ := (constantCoefficientPresheaf R X).exists_germ_eq z
  obtain ⟨V, hxV, s, rfl⟩ := (constantCoefficientPresheaf R X).exists_germ_eq z'
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply] at h
  obtain ⟨W, hxW, iWU, iWV, hW⟩ :=
    (singularCochainPresheaf R X 0).germ_eq x hxU hxV
      ((constantsToSingularCochainZero R X).app (.op U) r)
      ((constantsToSingularCochainZero R X).app (.op V) s) h
  let : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hrs : r = s := by
    apply constantSingularZeroCochain_injective R X (.op W)
    have hr := congrArg (fun k :
        (constantCoefficientPresheaf R X).obj (.op U) ⟶
          (singularCochainPresheaf R X 0).obj (.op W) ↦ k r)
      ((constantsToSingularCochainZero R X).naturality iWU.op)
    have hs := congrArg (fun k :
        (constantCoefficientPresheaf R X).obj (.op V) ⟶
          (singularCochainPresheaf R X 0).obj (.op W) ↦ k s)
      ((constantsToSingularCochainZero R X).naturality iWV.op)
    change constantSingularZeroCochain R X (.op W) r =
      (singularCochainPresheaf R X 0).map iWU.op
        ((constantsToSingularCochainZero R X).app (.op U) r) at hr
    change constantSingularZeroCochain R X (.op W) s =
      (singularCochainPresheaf R X 0).map iWV.op
        ((constantsToSingularCochainZero R X).app (.op V) s) at hs
    exact hr.trans (hW.trans hs.symm)
  subst s
  rw [← (constantCoefficientPresheaf R X).germ_res_apply iWU x hxW,
    ← (constantCoefficientPresheaf R X).germ_res_apply iWV x hxW]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- In a locally path-connected space, a singular zero-cocycle is constant on a smaller open
neighborhood of any chosen point. -/
lemma exists_local_constantSingularZeroCochain [LocallyPathConnectedSpace X]
    (x : X) (U : Opens X) (hx : x ∈ U)
    (φ : OpenCochains R X (.op U) 0)
    (hφ : (singularCochainCoboundary R X 0).app (.op U) φ = 0) :
    ∃ (V : Opens X) (_hxV : x ∈ V) (i : V ⟶ U) (r : R),
      constantSingularZeroCochain R X (.op V) r =
        (singularCochainPresheaf R X 0).map i.op φ := by
  let V : Opens X := ⟨pathComponentIn U x, U.2.pathComponentIn x⟩
  have hxV : x ∈ V := mem_pathComponentIn_self hx
  let i : V ⟶ U := homOfLE pathComponentIn_subset
  let : PathConnectedSpace V :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_pathComponentIn hx)
  let φV := (singularCochainPresheaf R X 0).map i.op φ
  have hφV : (singularCochainCoboundary R X 0).app (.op V) φV = 0 := by
    dsimp [φV]
    rw [← ConcreteCategory.comp_apply,
      (singularCochainCoboundary R X 0).naturality,
      ConcreteCategory.comp_apply, hφ, map_zero]
  obtain ⟨r, hr⟩ :=
    exists_eq_constantSingularZeroCochain_of_pathConnected R X (.op V) φV hφV
  exact ⟨V, hxV, i, r, hr⟩

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

set_option backward.isDefEq.respectTransparency false in
/-- On a locally path-connected space, the augmented singular zero-cochain sheaf complex is
exact. This identifies the kernel of the first coboundary with the constant sheaf. -/
lemma constantsToSingularCochainSheafShortComplex_exact [LocallyPathConnectedSpace X] :
    (constantsToSingularCochainSheafShortComplex R X).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  let stalk := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hP : ((constantsToSingularCochainPresheafShortComplex R X).map stalk).Exact :=
    stalkExact_of_locallyPrimitive X
      (constantsToSingularCochainPresheafShortComplex R X) (by
        intro y U hyU φ hφ
        change (singularCochainCoboundary R X 0).app (.op U) φ = 0 at hφ
        exact exists_local_constantSingularZeroCochain R X y U hyU φ hφ) x
  let unit := constantsToSingularCochainShortComplexSheafificationUnit R X
  let η := (stalk.mapShortComplex).map unit
  let : IsIso η.τ₁ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
      (constantCoefficientPresheaf R X)
  let : IsIso η.τ₂ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
      (singularCochainPresheaf R X 0)
  let : IsIso η.τ₃ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
      (singularCochainPresheaf R X 1)
  let : IsIso η := ShortComplex.isIso_of_isIso η
  exact ShortComplex.exact_of_iso (asIso η) hP

set_option backward.isDefEq.respectTransparency false in
/-- The sheafified inclusion of constants into singular zero-cochains is a monomorphism. -/
lemma constantsToSingularCochainZeroSheaf_mono :
    Mono (constantsToSingularCochainZeroSheaf R X) := by
  rw [TopCat.Presheaf.mono_iff_stalk_mono]
  intro x
  let stalk := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let unit := constantsToSingularCochainShortComplexSheafificationUnit R X
  let S := (constantsToSingularCochainPresheafShortComplex R X).map stalk
  let T := (constantsToSingularCochainSheafShortComplex R X).map
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ stalk)
  let η : S ⟶ T := (stalk.mapShortComplex).map unit
  let : IsIso η.τ₁ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
      (constantCoefficientPresheaf R X)
  let : IsIso η.τ₂ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
      (singularCochainPresheaf R X 0)
  let : Mono S.f := constantsToSingularCochainZero_stalk_mono R X x
  change Mono T.f
  have h : T.f = inv η.τ₁ ≫ S.f ≫ η.τ₂ := by
    rw [← cancel_epi η.τ₁, η.comm₁₂]
    simp
  rw [h]
  infer_instance

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

set_option backward.isDefEq.respectTransparency false in
/-- On a locally path-connected space, the constant-to-singular comparison is a
quasi-isomorphism in degree zero. -/
lemma constantsToSingularCochainSheafComplex_quasiIsoAt_zero
    [LocallyPathConnectedSpace X] :
    QuasiIsoAt (constantsToSingularCochainSheafComplex R X) 0 := by
  rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
  · exact ⟨constantsToSingularCochainSheafShortComplex_exact R X,
      constantsToSingularCochainZeroSheaf_mono R X⟩
  all_goals simp [singularCochainSheafComplex]

set_option backward.isDefEq.respectTransparency false in
/-- A neighborhood-wise primitive condition makes the constant-to-singular comparison a
quasi-isomorphism in positive degree. In degree `n + 1` the constant sheaf complex is already
exact, so the claim follows from exactness of the singular-cochain sheaf complex there. -/
lemma constantsToSingularCochainSheafComplex_quasiIsoAt_succ_of_locallyPrimitive (n : ℕ)
    (hlocal : ∀ (x : X) (U : Opens X) (_hx : x ∈ U)
      (φ : OpenCochains R X (.op U) (n + 1)),
        (singularCochainCoboundary R X (n + 1)).app (.op U) φ = 0 →
        ∃ (V : Opens X) (_hxV : x ∈ V) (i : V ⟶ U)
          (ψ : OpenCochains R X (.op V) n),
          (singularCochainCoboundary R X n).app (.op V) ψ =
            (singularCochainPresheaf R X (n + 1)).map i.op φ) :
    QuasiIsoAt (constantsToSingularCochainSheafComplex R X) (n + 1) := by
  rw [quasiIsoAt_iff_exactAt _ _
    (CochainComplex.exactAt_succ_single_obj (constantCoefficientSheaf R X) n)]
  exact singularCochainSheafComplex_exactAt_succ_of_locallyPrimitive R X n hlocal

set_option backward.isDefEq.respectTransparency false in
/-- A basis of open contractible neighborhoods supplies primitives for closed singular
cochains after shrinking. -/
lemma exists_local_singularCochain_primitive_of_contractibleOpenBasis
    (hbasis : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ (V : Opens X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (n : ℕ) (x : X) (U : Opens X) (hxU : x ∈ U)
    (φ : OpenCochains R X (.op U) (n + 1))
    (hφ : (singularCochainCoboundary R X (n + 1)).app (.op U) φ = 0) :
    ∃ (V : Opens X) (_hxV : x ∈ V) (i : V ⟶ U)
      (ψ : OpenCochains R X (.op V) n),
      (singularCochainCoboundary R X n).app (.op V) ψ =
        (singularCochainPresheaf R X (n + 1)).map i.op φ := by
  obtain ⟨V, hxV, hVcontractible, hVU⟩ := hbasis x U hxU
  let i : V ⟶ U := homOfLE hVU
  let K := (openSingularChainComplexFunctor R X).obj V
  let φV : OpenCochains R X (.op V) (n + 1) :=
    (singularCochainPresheaf R X (n + 1)).map i.op φ
  let : ContractibleSpace V := hVcontractible
  have hK : K.ExactAt (n + 1) :=
    singularChainComplex_exactAt_of_contractible R V (n + 1) (by lia)
  have hφV : (K.d (n + 2) (n + 1)).hom.dualMap φV = 0 := by
    change (singularCochainCoboundary R X (n + 1)).app (.op V) φV = 0
    dsimp [φV]
    rw [← ConcreteCategory.comp_apply,
      (singularCochainCoboundary R X (n + 1)).naturality,
      ConcreteCategory.comp_apply, hφ, map_zero]
  have hker : φV ∈ LinearMap.ker (K.d (n + 2) (n + 1)).hom.dualMap := hφV
  rw [← K.dual_differentials_range_eq_ker_of_exactAt n hK] at hker
  obtain ⟨ψ, hψ⟩ := hker
  exact ⟨V, hxV, i, ψ, hψ⟩

/-- On a space with a basis of open contractible neighborhoods, the constant-to-singular
comparison is a quasi-isomorphism in every positive degree. -/
lemma constantsToSingularCochainSheafComplex_quasiIsoAt_succ_of_contractibleOpenBasis
    (hbasis : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ (V : Opens X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (n : ℕ) :
    QuasiIsoAt (constantsToSingularCochainSheafComplex R X) (n + 1) :=
  constantsToSingularCochainSheafComplex_quasiIsoAt_succ_of_locallyPrimitive R X n
    (exists_local_singularCochain_primitive_of_contractibleOpenBasis R X hbasis n)

end AlgebraicTopology.Singular
