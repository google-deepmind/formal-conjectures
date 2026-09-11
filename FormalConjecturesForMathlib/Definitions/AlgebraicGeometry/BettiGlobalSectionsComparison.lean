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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.BettiSheafComparison
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.FlasqueQuasiIsoGlobalSections
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.InjectiveFlasque
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularSubdivisionCochainSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# Betti cohomology and global sections

This file identifies rational singular cohomology with the cohomology of the global-section
complex of the sheafified singular-cochain resolution on a paracompact Hausdorff space. It also
computes the hypercohomology of that resolution on a hereditarily paracompact Hausdorff space.

The derived comparison uses a bounded-below termwise-injective replacement. The mapping-cone
argument in `FlasqueQuasiIsoGlobalSections` proves that its quasi-isomorphism remains a
quasi-isomorphism after taking global sections. Thus no spectral sequence or acyclic-resolution
theorem is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace HomologicalComplex

universe u v

variable {C D : Type u} [Category C] [Category D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  {i i' : Type v} {c : ComplexShape i} {c' : ComplexShape i'}
  (F : C ⥤ D) [F.Additive] (K : HomologicalComplex C c)
  (e : c.Embedding c') [e.IsRelIff]

set_option backward.isDefEq.respectTransparency.types false in
/-- Componentwise form of the fact that an additive functor preserves extension by zero. -/
def mapExtendXIsoAux : (x : Option i) →
    F.obj (HomologicalComplex.extend.X K x) ≅
      HomologicalComplex.extend.X ((F.mapHomologicalComplex c).obj K) x
  | some _ => Iso.refl _
  | none => F.mapZeroObject

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
lemma mapExtendXIsoAux_d (x y : Option i) :
    (mapExtendXIsoAux F K x).hom ≫
        HomologicalComplex.extend.d ((F.mapHomologicalComplex c).obj K) x y =
      F.map (HomologicalComplex.extend.d K x y) ≫
        (mapExtendXIsoAux F K y).hom := by
  cases x with
  | none =>
      cases y with
      | none =>
          dsimp [mapExtendXIsoAux, HomologicalComplex.extend.d]
          rw [Functor.map_zero, Limits.comp_zero, Limits.zero_comp]
      | some y =>
          dsimp [mapExtendXIsoAux, HomologicalComplex.extend.d]
          rw [Functor.map_zero, Limits.comp_zero, Limits.zero_comp]
  | some x =>
      cases y with
      | none =>
          dsimp [mapExtendXIsoAux, HomologicalComplex.extend.d]
          rw [Functor.map_zero, Category.id_comp, Limits.zero_comp]
      | some y =>
          dsimp [mapExtendXIsoAux, HomologicalComplex.extend.d]
          rw [Category.id_comp, Category.comp_id]
          exact Functor.mapHomologicalComplex_obj_d F c K x y

set_option backward.isDefEq.respectTransparency.types false in
/-- An additive functor commutes degreewise with extension of a homological complex by zero. -/
def mapExtendXIso (q : i') :
    ((F.mapHomologicalComplex c').obj (K.extend e)).X q ≅
      (((F.mapHomologicalComplex c).obj K).extend e).X q :=
  mapExtendXIsoAux F K (e.r q)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- An additive functor commutes with extension of a homological complex by zero. -/
def mapExtendIso :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  HomologicalComplex.Hom.isoOfComponents (mapExtendXIso F K e) (by
    intro p q hpq
    change (mapExtendXIso F K e p).hom ≫
          HomologicalComplex.extend.d ((F.mapHomologicalComplex c).obj K)
            (e.r p) (e.r q) =
        F.map (HomologicalComplex.extend.d K (e.r p) (e.r q)) ≫
          (mapExtendXIso F K e q).hom
    dsimp only [mapExtendXIso]
    exact mapExtendXIsoAux_d F K (e.r p) (e.r q))

end HomologicalComplex

namespace CochainComplex.HomComplex

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The Hom complex from an object placed in degree zero is the degreewise preadditive
coyoneda functor applied to the target complex. -/
def fromSingleZeroIsoPreadditiveCoyoneda (X : C) (K : CochainComplex C ℤ) :
    CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj X) K ≅
      ((preadditiveCoyoneda.obj (.op X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (Cochain.fromSingleEquiv (p := 0) (q := n) (n := n)
      (zero_add n)).toAddCommGrpIso)
    (by
      intro i j hij
      apply AddCommGrpCat.hom_ext
      ext z
      obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z i (zero_add i)
      have he : Cochain.fromSingleEquiv (zero_add j)
          (CochainComplex.HomComplex.δ i j
            (Cochain.fromSingleMk f (zero_add i))) = f ≫ K.d i j := by
        rw [Cochain.δ_fromSingleMk f (zero_add i) j j (zero_add j)]
        simp
      have hleft : (preadditiveCoyoneda.obj (.op X)).map (K.d i j)
          (Cochain.fromSingleEquiv (zero_add i)
            (Cochain.fromSingleMk f (zero_add i))) = f ≫ K.d i j := by
        rw [Cochain.fromSingleEquiv_fromSingleMk]
        rfl
      have hcalc := hleft.trans he.symm
      simp only [AddCommGrpCat.comp_apply, AddEquiv.toAddCommGrpIso_hom,
        Functor.mapHomologicalComplex_obj_d]
      convert hcalc using 1 <;> rfl)

end CochainComplex.HomComplex

namespace TopCat.Sheaf

section

variable {Y : TopCat.{0}}

/-- Morphisms from the constant integer sheaf are the same as global sections. This is the
degree-zero adjunction underlying the global-sections comparison below. -/
def integerConstantHomEquivGlobalSections
    (F : TopCat.Sheaf AddCommGrpCat Y) :
    ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ) ⟶ F) ≃
      F.obj.obj (.op (⊤ : Opens Y)) :=
  ((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat
      isTerminalTop).homEquiv (AddCommGrpCat.of ℤ) F).trans <|
    ConcreteCategory.homEquiv.trans (zmultiplesHom (F.obj.obj (.op ⊤))).symm

/-- Additive form of `integerConstantHomEquivGlobalSections`. The explicit local Hom-group
instance avoids depending on reducibility-sensitive typeclass search through the sheaf
subcategory. -/
def integerConstantHomAddEquivGlobalSections
    (F : TopCat.Sheaf AddCommGrpCat Y) :
    letI : AddCommGroup
        ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ) ⟶ F) :=
      (inferInstance : Preadditive (TopCat.Sheaf AddCommGrpCat Y)).homGroup _ _
    ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ) ⟶ F) ≃+
      F.obj.obj (.op (⊤ : Opens Y)) := by
  letI : AddCommGroup
      ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ) ⟶ F) :=
    (inferInstance : Preadditive (TopCat.Sheaf AddCommGrpCat Y)).homGroup _ _
  exact ((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat
      isTerminalTop).homAddEquiv (AddCommGrpCat.of ℤ) F).trans <|
    AddCommGrpCat.homAddEquiv.trans (zmultiplesAddHom (F.obj.obj (.op ⊤))).symm

/-- The constant-integer/global-sections equivalence is natural in the sheaf. -/
lemma integerConstantHomEquivGlobalSections_naturality
    {F G : TopCat.Sheaf AddCommGrpCat Y} (f : F ⟶ G)
    (g : (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ) ⟶ F) :
    integerConstantHomEquivGlobalSections G (g ≫ f) =
      f.hom.app (.op (⊤ : Opens Y))
        (integerConstantHomEquivGlobalSections F g) := by
  have h := (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat
    isTerminalTop).homEquiv_naturality_right g f
  exact ConcreteCategory.congr_hom h (1 : ℤ)

end

/-- The integer sheaf placed in cohomological degree zero. -/
def integerConstantSingleComplex (Y : TopCat.{0}) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ :=
  (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat Y) 0).obj
    ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ))

/-- Evaluation of an integer-indexed sheaf complex on the top open subset. -/
def globalSectionsComplexInt (Y : TopCat.{0})
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) :
    CochainComplex AddCommGrpCat ℤ :=
  IsFlasque.BoundedBelowComplex.globalSectionsComplex K

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The additive constant-sheaf adjunction identifies the coyoneda functor represented by the
constant integer sheaf with the global-sections functor. -/
def integerConstantHomIsoGlobalSectionsFunctor (Y : TopCat.{0}) :
    preadditiveCoyoneda.obj
        (.op ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ))) ≅
      IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y :=
  NatIso.ofComponents
    (fun F ↦ (integerConstantHomAddEquivGlobalSections F).toAddCommGrpIso)
    (fun {F G} f ↦ by
      apply AddCommGrpCat.hom_ext
      ext g
      change f.hom.app (.op (⊤ : Opens Y))
          (integerConstantHomEquivGlobalSections F g) =
        integerConstantHomEquivGlobalSections G (g ≫ f)
      exact (integerConstantHomEquivGlobalSections_naturality f g).symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The Hom complex from the degree-zero integer sheaf is canonically the complex of global
sections. -/
def homComplexSingleIntegerIsoGlobalSections
    (Y : TopCat.{0}) (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) :
    CochainComplex.HomComplex (integerConstantSingleComplex Y) K ≅
      globalSectionsComplexInt Y K := by
  let pre := (inferInstance : Preadditive (TopCat.Sheaf AddCommGrpCat Y))
  letI : Preadditive (TopCat.Sheaf AddCommGrpCat Y) := pre
  let : (IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  exact CochainComplex.HomComplex.fromSingleZeroIsoPreadditiveCoyoneda
      ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)) K ≪≫
    (NatIso.mapHomologicalComplex (integerConstantHomIsoGlobalSectionsFunctor Y)
      (ComplexShape.up ℤ)).app K

end TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

/-- The integer constant-sheaf complex used to define hypercohomology is the degree-zero
integer constant sheaf, after extending its natural-number grading to integer degrees. -/
def constantIntegerSheafComplexIntIsoSingle :
    constantIntegerSheafComplexInt X ≅
      TopCat.Sheaf.integerConstantSingleComplex
        (TopCat.of (ComplexPoint X)) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
    (constantIntegerSheaf X) 0 0 rfl

/-- Every integer-indexed term of the singular-cochain resolution is flasque on a hereditarily
paracompact Hausdorff complex-point space. Negative terms are zero, and nonnegative terms are
the corresponding natural-number-indexed singular-cochain sheaves. -/
theorem singularCochainSheafComplexInt_isFlasque
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℤ) :
    TopCat.Sheaf.IsFlasque ((singularCochainSheafComplexInt X ℚ).X n) := by
  by_cases hn : ∃ m : ℕ, (m : ℤ) = n
  · obtain ⟨m, rfl⟩ := hn
    let e := (AlgebraicTopology.Singular.singularCochainSheafComplex ℚ
      (TopCat.of (ComplexPoint X))).extendXIso
        ComplexShape.embeddingUpNat (i := m) rfl
    let hP : TopCat.Presheaf.IsFlasque
        ((AlgebraicTopology.Singular.singularCochainSheafComplex ℚ
          (TopCat.of (ComplexPoint X))).X m).obj := by
      change TopCat.Sheaf.IsFlasque
        (AlgebraicTopology.Singular.singularCochainSheaf ℚ
          (TopCat.of (ComplexPoint X)) m)
      infer_instance
    change TopCat.Presheaf.IsFlasque
      ((singularCochainSheafComplexInt X ℚ).X (m : ℤ)).obj
    exact @AlgebraicTopology.Singular.presheaf_isFlasque_of_iso _ _ _
      ((TopCat.Sheaf.forget AddCommGrpCat
        (TopCat.of (ComplexPoint X))).mapIso e.symm) hP
  · apply TopCat.Sheaf.IsFlasque.of_isZero
    exact (AlgebraicTopology.Singular.singularCochainSheafComplex ℚ
      (TopCat.of (ComplexPoint X))).isZero_extend_X
        ComplexShape.embeddingUpNat n (fun i hi ↦ hn ⟨i, hi⟩)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Taking global sections commutes with extending the natural-number-indexed singular-cochain
sheaf complex by zero to integer degrees. -/
def globalSectionsSingularCochainComplexIntIsoExtend :
    TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X ℚ) ≅
      (AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℚ
        (TopCat.of (ComplexPoint X))).extend
          ComplexShape.embeddingUpNat := by
  let Y := TopCat.of (ComplexPoint X)
  let F := TopCat.Sheaf.forget AddCommGrpCat Y
  let E := (evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (.op ⊤)
  let G := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let K := AlgebraicTopology.Singular.singularCochainSheafComplex ℚ Y
  let : F.Additive := by dsimp [F]; infer_instance
  let : E.Additive := by dsimp [E]; infer_instance
  let eComp : F ⋙ E ≅ G := Iso.refl _
  exact HomologicalComplex.mapExtendIso G K ComplexShape.embeddingUpNat ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat).mapIso
      ((Functor.mapHomologicalComplexCompIso eComp (ComplexShape.up ℕ)).app K).symm

/-- If a K-injective resolution remains a quasi-isomorphism after taking global sections, then
the hypercohomology of the rational singular-cochain resolution is the homology of its own
global-section complex. The hypotheses are the precise resolution properties needed by the
construction; no acyclic-resolution theorem is assumed here. -/
def rationalSingularCochainHypercohomologyEquivGlobalSectionsOfResolution
    (I : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [I.IsKInjective]
    (i : singularCochainSheafComplexInt X ℚ ⟶ I) [QuasiIso i]
    [QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map i)]
    (n : ℤ) :
    RationalSingularCochainHypercohomology X n ≃
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X ℚ)).homology n := by
  let Y := TopCat.of (ComplexPoint X)
  let A := constantIntegerSheafComplexInt X
  let A' := TopCat.Sheaf.integerConstantSingleComplex Y
  let S := singularCochainSheafComplexInt X ℚ
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let e : A ≅ A' := constantIntegerSheafComplexIntIsoSingle X
  have hi : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) i := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  have he : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) e.inv := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  let e₁ := Localization.SmallShiftedHom.postcompEquiv
    (X := A) (Y := S) (Z := I) (a := n) i hi
  let e₂ := Localization.SmallShiftedHom.precompEquiv
    (X := A') (Y := A) (Z := I) (a := n) e.inv he
  let e₃ := (CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective
    (K := A') (L := I) (n := n)).symm
  let e₄ := (CochainComplex.HomComplex.homologyAddEquiv A' I n).symm.toEquiv
  let e₅ := (HomologicalComplex.homologyMapIso
    (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y I) n)
      |>.addCommGroupIsoToAddEquiv.toEquiv
  let : QuasiIso ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map i) := inferInstance
  let e₆ := (asIso (HomologicalComplex.homologyMap
    ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map i) n)).symm
      |>.addCommGroupIsoToAddEquiv.toEquiv
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans e₆))))

/-- On a hereditarily paracompact Hausdorff complex-point space, hypercohomology of the rational
singular-cochain resolution is computed by its global-section complex. This chooses Mathlib's
bounded-below termwise-injective replacement and proves that global sections preserve the
replacement quasi-isomorphism by the flasque mapping-cone argument. -/
def rationalSingularCochainHypercohomologyEquivGlobalSections
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℤ) :
    RationalSingularCochainHypercohomology X n ≃
      (TopCat.Sheaf.globalSectionsComplexInt
        (TopCat.of (ComplexPoint X))
        (singularCochainSheafComplexInt X ℚ)).homology n := by
  let Y := TopCat.of (ComplexPoint X)
  let S := singularCochainSheafComplexInt X ℚ
  let : S.IsStrictlyGE 0 := by
    dsimp [S, singularCochainSheafComplexInt]
    infer_instance
  choose I i _ _ _ using
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective S 0
  letI : I.IsKInjective := CochainComplex.isKInjective_of_injective I 0
  have hSflasque : ∀ q, (S.X q).IsFlasque :=
    fun q ↦ singularCochainSheafComplexInt_isFlasque X q
  have hIflasque : ∀ q, (I.X q).IsFlasque := fun _ ↦ inferInstance
  letI : QuasiIso
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
        ).mapHomologicalComplex (ComplexShape.up ℤ)).map i) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso
      i 0 0 hSflasque hIflasque
  exact rationalSingularCochainHypercohomologyEquivGlobalSectionsOfResolution
    X I i n

end AlgebraicGeometry.ComplexPoint

namespace AlgebraicTopology.Singular

universe u

variable (R : Type u) [Field R] (Y : TopCat.{u})

set_option backward.isDefEq.respectTransparency false in
/-- The short complex controlling degree-`n` cohomology of the full linear-dual cochain complex
is the reversed dual of the degree-`n` singular-chain short complex. -/
def linearDualCochainComplexScIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    K.linearDualCochainComplex.sc n ≅ (K.sc n).linearDual := by
  let D := K.linearDualCochainComplex
  have hprev : (ComplexShape.up ℕ).prev n = (ComplexShape.down ℕ).next n := by
    cases n <;> simp
  have hnext : (ComplexShape.up ℕ).next n = (ComplexShape.down ℕ).prev n := by simp
  refine D.isoSc' ((ComplexShape.down ℕ).next n) n
      ((ComplexShape.down ℕ).prev n) hprev hnext ≪≫
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · cases n with
    | zero =>
        simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
          HomologicalComplex.shortComplexFunctor'_obj_f]
        dsimp only [ShortComplex.linearDual, ShortComplex.moduleCatMk,
          HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
          HomologicalComplex.shortComplexFunctor']
        rw [ChainComplex.next_nat_zero]
        change ModuleCat.ofHom (K.d 0 0).hom.dualMap = D.d 0 0
        rw [K.shape 0 0 (by simp), D.shape 0 0 (by simp)]
        exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ LinearMap.ext fun _ ↦ map_zero φ)
    | succ n =>
        simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
          HomologicalComplex.shortComplexFunctor'_obj_f]
        dsimp only [ShortComplex.linearDual, ShortComplex.moduleCatMk,
          HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
          HomologicalComplex.shortComplexFunctor']
        rw [ChainComplex.next_nat_succ]
        change ModuleCat.ofHom (K.d (n + 1) n).hom.dualMap = D.d n (n + 1)
        exact (HomologicalComplex.linearDualCochainComplex_d K n).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
      HomologicalComplex.shortComplexFunctor'_obj_g]
    dsimp only [ShortComplex.linearDual, ShortComplex.moduleCatMk,
      HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor']
    rw [ChainComplex.prev]
    change ModuleCat.ofHom (K.d (n + 1) n).hom.dualMap = D.d n (n + 1)
    exact (HomologicalComplex.linearDualCochainComplex_d K n).symm

/-- Ordinary singular cohomology, presented as the homology of the algebraic-dual singular
cochain complex. -/
abbrev OrdinarySingularCohomology (n : ℕ) : ModuleCat.{u} R :=
  (SingularChainComplex R Y).linearDualCochainComplex.homology n

/-- Universal coefficients identify the full-complex presentation of ordinary singular
cohomology with the repository's existing dual-of-singular-homology type. -/
def ordinarySingularCohomologyEquivCohomology (n : ℕ) :
    OrdinarySingularCohomology R Y n ≃ₗ[R] Cohomology R Y n :=
  (ShortComplex.homologyMapIso
    (linearDualCochainComplexScIso R (SingularChainComplex R Y) n)).toLinearEquiv.trans
      ((SingularChainComplex R Y).sc n).linearDualHomologyEquiv

/-- Forgetting scalar multiplication commutes with taking the homology of the top-open singular
cochain complex. -/
def topOpenForgottenSingularCochainHomologyIso (n : ℕ) :
    (topOpenForgottenSingularCochainComplex R Y).homology n ≅
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat).obj
        ((TopOpenSingularChainComplex R Y).linearDualCochainComplex.homology n) :=
  ShortComplex.mapHomologyIso
    ((TopOpenSingularChainComplex R Y).linearDualCochainComplex.sc n)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat)

/-- Ordinary singular cohomology agrees with the homology of the raw singular-cochain
presheaf evaluated on the top open subset. -/
def ordinarySingularCohomologyEquivGlobalRaw (n : ℕ) :
    OrdinarySingularCohomology R Y n ≃+
      (globalRawSingularCochainComplex R Y).homology n :=
  ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapIso
      (HomologicalComplex.homologyMapIso
        (singularCochainComplexIsoTopOpen R Y) n)).addCommGroupIsoToAddEquiv |>.trans <|
    (topOpenForgottenSingularCochainHomologyIso R Y n).symm.addCommGroupIsoToAddEquiv |>.trans <|
      (HomologicalComplex.homologyMapIso
        (globalRawSingularCochainComplexIso R Y) n).symm.addCommGroupIsoToAddEquiv

end AlgebraicTopology.Singular

namespace AlgebraicTopology.Singular.HereditarilyParacompact

/-- On a paracompact Hausdorff space, ordinary rational singular cohomology is the cohomology of
the global-section complex of the chosen singular-cochain sheaf resolution. -/
def ordinaryRationalSingularCohomologyEquivGlobalSections
    (Y : TopCat.{0}) [ParacompactSpace Y] [T2Space Y] (n : ℕ) :
    AlgebraicTopology.Singular.OrdinarySingularCohomology ℚ Y n ≃+
      (AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℚ Y).homology n := by
  let := AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex_quasiIso
    (Y := Y)
  exact
    AlgebraicTopology.Singular.ordinarySingularCohomologyEquivGlobalRaw ℚ Y n |>.trans <|
      (asIso (HomologicalComplex.homologyMap
        (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex ℚ Y) n))
          |>.addCommGroupIsoToAddEquiv

/-- On a paracompact Hausdorff space, the repository's Betti cohomology type is the cohomology
of the global-section complex of the singular-cochain sheaf resolution. -/
def rationalSingularCohomologyEquivGlobalSections
    (Y : TopCat.{0}) [ParacompactSpace Y] [T2Space Y] (n : ℕ) :
    AlgebraicTopology.Singular.Cohomology ℚ Y n ≃+
      (AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℚ Y).homology n :=
  (AlgebraicTopology.Singular.ordinarySingularCohomologyEquivCohomology ℚ Y n).symm.toAddEquiv
    |>.trans (ordinaryRationalSingularCohomologyEquivGlobalSections Y n)

end AlgebraicTopology.Singular.HereditarilyParacompact

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

/-- On a hereditarily paracompact Hausdorff complex-point space, hypercohomology of the rational
singular-cochain resolution is the repository's existing rational singular cohomology type. -/
def rationalSingularCochainHypercohomologyEquivCohomology
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    RationalSingularCochainHypercohomology X (n : ℤ) ≃
      AlgebraicTopology.Singular.Cohomology ℚ
        (TopCat.of (ComplexPoint X)) n := by
  let Y := TopCat.of (ComplexPoint X)
  let K := AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℚ Y
  letI : ParacompactSpace (ComplexPoint X) :=
    (Homeomorph.Set.univ (ComplexPoint X)).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint X)))
  exact (rationalSingularCochainHypercohomologyEquivGlobalSections
      X (n : ℤ)).trans <|
    (HomologicalComplex.homologyMapIso
      (globalSectionsSingularCochainComplexIntIsoExtend X)
        (n : ℤ)).addCommGroupIsoToAddEquiv.toEquiv |>.trans <|
      (K.extendHomologyIso ComplexShape.embeddingUpNat rfl).addCommGroupIsoToAddEquiv.toEquiv
        |>.trans <|
        (AlgebraicTopology.Singular.HereditarilyParacompact.rationalSingularCohomologyEquivGlobalSections
          Y n).symm.toEquiv

/-- On a smooth complex scheme whose analytification is hereditarily paracompact Hausdorff,
rational constant-sheaf cohomology agrees with the repository's rational singular cohomology. -/
def rationalCohomologyEquivSingularCohomology
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    H^(n : ℤ)(X; ℚ) ≃
      AlgebraicTopology.Singular.Cohomology ℚ
        (TopCat.of (ComplexPoint X)) n :=
  (rationalCohomologySingularCochainEquiv X (n : ℤ)).trans
    (rationalSingularCochainHypercohomologyEquivCohomology X n)

end AlgebraicGeometry.ComplexPoint
