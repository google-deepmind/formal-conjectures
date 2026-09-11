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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularChainSheaf
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.RelativeHomotopyInvariance

/-!
# Stalks of the relative singular-chain presheaf

The key geometric fact is that a singular simplex avoiding a point has compact image and,
in a Hausdorff space, therefore avoids an open neighborhood of that point. This allows the
local relative chain complex to be identified with the colimit over open neighborhoods.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped Simplicial

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopCat.{u})

/-- Restriction of relative chains over the open neighborhoods of `x`. -/
def relativeChainNeighborhoodDiagram (x : X) : (OpenNhds x)ᵒᵖ ⥤ ChainCategory R :=
  (OpenNhds.inclusion x).op ⋙ openRelativeSingularChainComplexFunctor R X

set_option backward.isDefEq.respectTransparency false in
/-- The map from ambient to relative chains commutes with restriction of the support. -/
@[reassoc] lemma relativeChainProjection_supportInclusion {Z W : Set X} (h : Z ⊆ W) :
    relativeChainProjection R (TopPair.ofSubset Wᶜ) ≫
      (relativeChainFunctor R).map (supportInclusionPairMap X h) =
        relativeChainProjection R (TopPair.ofSubset Zᶜ) := by
  have hnat := TopPair.Homotopy.relativeChainProjection_naturality (R := R)
    (supportInclusionPairMap X h)
  change _ = ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).map
    (𝟙 X) ≫ _ at hnat
  calc
    _ = _ := hnat
    _ = 𝟙 _ ≫ relativeChainProjection R (TopPair.ofSubset Zᶜ) :=
      congrArg (fun f ↦ f ≫ relativeChainProjection R (TopPair.ofSubset Zᶜ))
        (((singularChainComplexFunctor (ModuleCat.{u} R)).obj
          (ModuleCat.of R R)).map_id X)
    _ = _ := Category.id_comp _

/-- Restricting every open neighborhood to the singleton gives a cocone of chain complexes. -/
def localRelativeChainCocone (x : X) : Cocone (relativeChainNeighborhoodDiagram R X x) where
  pt := (relativeChainFunctor R).obj (TopPair.ofSubset ({x} : Set X)ᶜ)
  ι :=
    { app U := (relativeChainFunctor R).map
        (supportInclusionPairMap X (Set.singleton_subset_iff.mpr U.unop.2))
      naturality {U V} i := by
        change (relativeChainFunctor R).map (supportInclusionPairMap X (leOfHom i.unop)) ≫
          (relativeChainFunctor R).map
            (supportInclusionPairMap X (Set.singleton_subset_iff.mpr V.unop.2)) = _
        rw [← Functor.map_comp, ← supportInclusionPairMap_trans]
        rfl }

/-- Every singular simplex in the complement of a point factors through the complement of
some open neighborhood of that point. Hausdorffness is used only to close its compact image. -/
lemma exists_openNhds_complement_simplex [T2Space X] (x : X) {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopPair.ofSubset ({x} : Set X)ᶜ).snd) _⦋n⦌) :
    ∃ (U : OpenNhds x)
      (τ : (TopCat.toSSet.obj (TopPair.ofSubset (U.1 : Set X)ᶜ).snd) _⦋n⦌),
      (TopCat.toSSet.map (TopPair.ofSubset (U.1 : Set X)ᶜ).map).app _ τ =
        (TopCat.toSSet.map (TopPair.ofSubset ({x} : Set X)ᶜ).map).app _ σ := by
  let f := (TopPair.ofSubset ({x} : Set X)ᶜ).snd.toSSetObjEquiv _ σ
  let g : C(stdSimplex ℝ (Fin (n + 1)), X) := ⟨fun t ↦ (f t).1,
    continuous_subtype_val.comp f.continuous⟩
  have hclosed : IsClosed (Set.range g) := (isCompact_range g.continuous).isClosed
  let U : OpenNhds x := ⟨⟨(Set.range g)ᶜ, hclosed.isOpen_compl⟩, by
    rintro ⟨t, ht⟩
    exact (f t).2 (by simpa only [g, ContinuousMap.coe_mk, Set.mem_singleton_iff] using ht)⟩
  have hg : ∀ t, g t ∈ (U.1 : Set X)ᶜ := fun t h ↦ h (Set.mem_range_self t)
  let τ : (TopCat.toSSet.obj (TopPair.ofSubset (U.1 : Set X)ᶜ).snd) _⦋n⦌ :=
    ((TopPair.ofSubset (U.1 : Set X)ᶜ).snd.toSSetObjEquiv _).symm
      ⟨fun t ↦ ⟨g t, hg t⟩, g.continuous.subtype_mk hg⟩
  refine ⟨U, τ, ?_⟩
  apply (X.toSSetObjEquiv _).injective
  ext t
  rfl

/-- The map from ambient chains induced by a neighborhood cocone. -/
def absoluteChainMapOfNeighborhoodCocone (x : X)
    (c : Cocone (relativeChainNeighborhoodDiagram R X x)) :
    ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj X ⟶ c.pt :=
  relativeChainProjection R (TopPair.ofSubset ((⊤ : Opens X) : Set X)ᶜ) ≫
    c.ι.app (.op ⟨⊤, trivial⟩)

set_option backward.isDefEq.respectTransparency false in
/-- A neighborhood cocone induces the same ambient-chain map through each of its objects. -/
lemma absoluteChainMapOfNeighborhoodCocone_eq (x : X)
    (c : Cocone (relativeChainNeighborhoodDiagram R X x)) (U : OpenNhds x) :
    absoluteChainMapOfNeighborhoodCocone R X x c =
      relativeChainProjection R (TopPair.ofSubset (U.1 : Set X)ᶜ) ≫ c.ι.app (.op U) := by
  let i : U ⟶ (⟨⊤, trivial⟩ : OpenNhds x) := homOfLE le_top
  have h := c.w i.op
  change (relativeChainFunctor R).map (supportInclusionPairMap X (leOfHom i)) ≫
    c.ι.app (.op U) = c.ι.app (.op ⟨⊤, trivial⟩) at h
  rw [absoluteChainMapOfNeighborhoodCocone, ← h, ← Category.assoc,
    relativeChainProjection_supportInclusion]

set_option backward.isDefEq.respectTransparency false in
/-- A simplex from the subspace vanishes under the relative-chain projection. -/
lemma iota_subspace_relativeChainProjection (P : TopPair.{u}) {n : ℕ}
    (σ : (TopCat.toSSet.obj P.snd) _⦋n⦌) :
    (TopCat.toSSet.obj P.fst).ιChainComplex
        ((TopCat.toSSet.map P.map).app _ σ) ≫ (relativeChainProjection R P).f n = 0 := by
  rw [← SSet.ι_chainComplexMap_f, Category.assoc]
  have h := congrArg (fun f ↦ f.f n) (subspaceChainMap_relativeChainProjection R P)
  change (SSet.chainComplexMap (TopCat.toSSet.map P.map) (ModuleCat.of R R)).f n ≫
    (relativeChainProjection R P).f n = 0 at h
  rw [h, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Compactness of each singular simplex shows that every neighborhood cocone kills the
entire chain complex of the point complement. No finite-chain representatives are chosen. -/
lemma subspaceChainMap_absoluteChainMapOfNeighborhoodCocone [T2Space X] (x : X)
    (c : Cocone (relativeChainNeighborhoodDiagram R X x)) :
    ((chainPairFunctor R).obj (TopPair.ofSubset ({x} : Set X)ᶜ)).hom ≫
      absoluteChainMapOfNeighborhoodCocone R X x c = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  change (SSet.chainComplexMap
      (TopCat.toSSet.map (TopPair.ofSubset ({x} : Set X)ᶜ).map)
      (ModuleCat.of R R)).f n ≫
        (absoluteChainMapOfNeighborhoodCocone R X x c).f n = 0
  apply SSet.chainComplex_hom_ext
  intro σ
  obtain ⟨U, τ, hτ⟩ := exists_openNhds_complement_simplex X x σ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, ← hτ]
  have h := congrArg (fun f ↦ f.f n) (absoluteChainMapOfNeighborhoodCocone_eq R X x c U)
  change (absoluteChainMapOfNeighborhoodCocone R X x c).f n =
    (relativeChainProjection R (TopPair.ofSubset (U.1 : Set X)ᶜ)).f n ≫
      (c.ι.app (.op U)).f n at h
  rw [h, ← Category.assoc, comp_zero]
  exact (congrArg (fun f ↦ f ≫ (c.ι.app (.op U)).f n)
    (iota_subspace_relativeChainProjection R (TopPair.ofSubset (U.1 : Set X)ᶜ) τ)).trans
      zero_comp

/-- The universal map from local relative chains to an arbitrary neighborhood cocone. -/
def localRelativeChainCoconeDesc [T2Space X] (x : X)
    (c : Cocone (relativeChainNeighborhoodDiagram R X x)) :
    (localRelativeChainCocone R X x).pt ⟶ c.pt :=
  cokernel.desc ((chainPairFunctor R).obj (TopPair.ofSubset ({x} : Set X)ᶜ)).hom
    (absoluteChainMapOfNeighborhoodCocone R X x c)
    (subspaceChainMap_absoluteChainMapOfNeighborhoodCocone R X x c)

/-- The colimit-descent map recovers the ambient-chain map under the quotient projection. -/
@[reassoc] lemma relativeChainProjection_localRelativeChainCoconeDesc [T2Space X] (x : X)
    (c : Cocone (relativeChainNeighborhoodDiagram R X x)) :
    relativeChainProjection R (TopPair.ofSubset ({x} : Set X)ᶜ) ≫
      localRelativeChainCoconeDesc R X x c = absoluteChainMapOfNeighborhoodCocone R X x c :=
  cokernel.π_desc _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The actual local relative chain complex is the colimit over open neighborhoods.
The proof uses the quotient universal property and compactness of individual simplices. -/
def localRelativeChainCoconeIsColimit [T2Space X] (x : X) :
    IsColimit (localRelativeChainCocone R X x) where
  desc c := localRelativeChainCoconeDesc R X x c
  fac c U := by
    let P := TopPair.ofSubset (U.unop.1 : Set X)ᶜ
    have : Epi (relativeChainProjection R P) := by
      dsimp [relativeChainProjection]
      infer_instance
    apply (cancel_epi (relativeChainProjection R P)).mp
    change relativeChainProjection R P ≫
      (relativeChainFunctor R).map
        (supportInclusionPairMap X (Set.singleton_subset_iff.mpr U.unop.2)) ≫
          localRelativeChainCoconeDesc R X x c = _
    rw [relativeChainProjection_supportInclusion_assoc,
      relativeChainProjection_localRelativeChainCoconeDesc,
      absoluteChainMapOfNeighborhoodCocone_eq R X x c U.unop]
  uniq c m hm := by
    have : Epi (relativeChainProjection R (TopPair.ofSubset ({x} : Set X)ᶜ)) := by
      dsimp [relativeChainProjection]
      infer_instance
    apply (cancel_epi (relativeChainProjection R (TopPair.ofSubset ({x} : Set X)ᶜ))).mp
    rw [relativeChainProjection_localRelativeChainCoconeDesc,
      absoluteChainMapOfNeighborhoodCocone]
    have h := hm (.op ⟨⊤, trivial⟩)
    rw [← h, ← Category.assoc]
    change _ = (relativeChainProjection R (TopPair.ofSubset ((⊤ : Opens X) : Set X)ᶜ) ≫
      (relativeChainFunctor R).map (supportInclusionPairMap X _)) ≫ m
    rw [relativeChainProjection_supportInclusion]

/-- Evaluating a chain complex in degree `n` and forgetting its scalar structure. -/
def chainDegreeAdditiveFunctor (n : ℕ) : ChainCategory R ⥤ AddCommGrpCat.{u} :=
  HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n ⋙
    forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

instance chainDegreeAdditiveFunctor_preservesColimits (n : ℕ) :
    PreservesColimitsOfSize.{u, u} (chainDegreeAdditiveFunctor R n) where
  preservesColimitsOfShape {J} _ := by
    unfold chainDegreeAdditiveFunctor
    infer_instance

/-- The stalk of relative `n`-chains is canonically the relative `n`-chains of the point
complement. This is a chain-level isomorphism, not just a homology comparison. -/
def singularChainPresheafStalkIso [T2Space X] (x : X) (n : ℕ) :
    (singularChainPresheaf R X n).stalk x ≅
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        (((relativeChainFunctor R).obj (TopPair.ofSubset ({x} : Set X)ᶜ)).X n) :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (isColimitOfPreserves (chainDegreeAdditiveFunctor R n)
      (localRelativeChainCoconeIsColimit R X x))

/-- On a germ represented over `U`, the stalk isomorphism is the actual restriction map from
`(X, X ∖ U)` to `(X, X ∖ {x})`. -/
@[reassoc] lemma singularChainPresheafStalkIso_germ [T2Space X]
    (x : X) (U : Opens X) (hx : x ∈ U) (n : ℕ) :
    (singularChainPresheaf R X n).germ U x hx ≫
        (singularChainPresheafStalkIso R X x n).hom =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        (((relativeChainFunctor R).map
          (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx))).f n) :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom
    (isColimitOfPreserves (chainDegreeAdditiveFunctor R n)
      (localRelativeChainCoconeIsColimit R X x)) (.op ⟨U, hx⟩)

set_option backward.isDefEq.respectTransparency false in
/-- The stalk identification respects the actual local relative singular boundary. -/
@[reassoc] lemma singularChainPresheafStalkIso_boundary [T2Space X] (x : X) (n : ℕ) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (singularChainBoundary R X n) ≫
        (singularChainPresheafStalkIso R X x n).hom =
      (singularChainPresheafStalkIso R X x (n + 1)).hom ≫
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
          (((relativeChainFunctor R).obj (TopPair.ofSubset ({x} : Set X)ᶜ)).d (n + 1) n) := by
  apply (singularChainPresheaf R X (n + 1)).stalk_hom_ext
  intro U hx
  rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ,
    Category.assoc, singularChainPresheafStalkIso_germ,
    ← Category.assoc, singularChainPresheafStalkIso_germ]
  exact congrArg ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map)
    (((relativeChainFunctor R).map
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx))).comm (n + 1) n).symm

/-- Stalks of the presheaf complex identify with the full local relative singular-chain
complex, including the differential. -/
def singularChainPresheafComplexStalkIso [T2Space X] (x : X) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (singularChainPresheafComplex R X) ≅
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        ((relativeChainFunctor R).obj (TopPair.ofSubset ({x} : Set X)ᶜ)) :=
  HomologicalComplex.Hom.isoOfComponents (singularChainPresheafStalkIso R X x) (by
    intro i j hij
    obtain rfl := hij
    change (singularChainPresheafStalkIso R X x (j + 1)).hom ≫ _ =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((singularChainPresheafComplex R X).d (j + 1) j) ≫
          (singularChainPresheafStalkIso R X x j).hom
    rw [singularChainPresheafComplex_d]
    exact (singularChainPresheafStalkIso_boundary R X x j).symm)

/-- The stalk of the constructed relative singular-chain sheaf complex is the actual local
relative singular-chain complex. This isomorphism requires only Hausdorffness of `X`. -/
def singularChainSheafStalkIso [T2Space X] (x : X) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
      (((TopCat.Sheaf.forget AddCommGrpCat.{u} X).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (singularChainSheafComplex R X)) ≅
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        ((relativeChainFunctor R).obj (TopPair.ofSubset ({x} : Set X)ᶜ)) :=
  (singularChainSheafificationStalkIso R X x).symm ≪≫
    singularChainPresheafComplexStalkIso R X x

/-- Homology of the stalk complex is precisely the ordinary local relative singular homology.
The scalar-forgetting comparison is the canonical homology comparison for an exact functor. -/
def singularChainSheafStalkHomologyIso [T2Space X] (x : X) (n : ℕ) :
    (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
      (((TopCat.Sheaf.forget AddCommGrpCat.{u} X).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (singularChainSheafComplex R X))).homology n ≅
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        (RelativeHomology R (TopPair.ofSubset ({x} : Set X)ᶜ) n) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n).mapIso
      (singularChainSheafStalkIso R X x) ≪≫
    (((relativeChainFunctor R).obj (TopPair.ofSubset ({x} : Set X)ᶜ)).sc n).mapHomologyIso
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

end AlgebraicTopology.Singular
