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

public import FormalConjecturesForMathlib.AlgebraicTopology.SingularBarycentricAllDegrees

import FormalConjecturesForMathlib.AlgebraicTopology.SingularBarycentricOuterFaces
import Mathlib.Logic.Equiv.PartialEquiv

/-!
This module is ported from Paul Lezeau's corresponding file in
`sphere-six-complex` pull request #49, under the Apache-2.0 license.

# Affine realization of barycentric flags as singular simplices

A simplex in the nerve model of barycentric subdivision is a flag of nonempty faces.  This
file sends such a flag to the affine singular simplex whose vertices are the barycenters of
those faces.  The construction is deliberately degreewise: the codimension-one face formula
is the piece needed to transport the combinatorial subdivision-chain boundary calculation to
ordinary singular chains.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits PartialOrder Simplicial

namespace AlgebraicTopology.Singular

/-- The affine combination of a finite family of points in a standard simplex. -/
public noncomputable def stdSimplexAffineCombination
    {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X → stdSimplex ℝ Y) (w : stdSimplex ℝ X) :
    stdSimplex ℝ Y :=
  ⟨fun y ↦ ∑ x, w x * p x y,
    ⟨fun y ↦ Finset.sum_nonneg (fun x _ ↦ mul_nonneg (w.2.1 x) ((p x).2.1 y)),
      by
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, stdSimplex.sum_eq_one, mul_one]⟩⟩

@[simp]
public theorem stdSimplexAffineCombination_apply
    {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X → stdSimplex ℝ Y) (w : stdSimplex ℝ X) (y : Y) :
    stdSimplexAffineCombination p w y = ∑ x, w x * p x y :=
  rfl

/-- Affine combination varies continuously with its simplex of coefficients. -/
public theorem continuous_stdSimplexAffineCombination
    {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X → stdSimplex ℝ Y) :
    Continuous (stdSimplexAffineCombination p) := by
  unfold stdSimplexAffineCombination
  apply Continuous.subtype_mk
  apply continuous_pi
  intro y
  exact continuous_finsetSum _ fun x _ ↦
    ((continuous_apply x).comp continuous_subtype_val).mul continuous_const

/-- Reindexing the coefficients reindexes the vertices of an affine simplex. -/
public theorem stdSimplexAffineCombination_map
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (f : X → Y) (p : Y → stdSimplex ℝ Z) (w : stdSimplex ℝ X) :
    stdSimplexAffineCombination p (stdSimplex.map f w) =
      stdSimplexAffineCombination (p ∘ f) w := by
  classical
  ext z
  simp only [stdSimplexAffineCombination_apply, stdSimplex.map_coe,
    FunOnFinite.linearMap_apply_apply, Function.comp_apply, Finset.sum_mul]
  calc
    ∑ y, ∑ x with f x = y, w x * p y z =
        ∑ y, ∑ x with f x = y, w x * p (f x) z := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = ∑ x, w x * p (f x) z :=
      Finset.sum_fiberwise Finset.univ f (fun x ↦ w x * p (f x) z)

/-- An injective reindexing preserves the coefficient over every point of its image. -/
@[simp]
public theorem stdSimplex_map_apply_injective
    {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (hf : Function.Injective f)
    (w : stdSimplex ℝ X) (x : X) :
    stdSimplex.map f w (f x) = w x := by
  classical
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, hf.eq_iff]
  have hfilter : Finset.univ.filter (fun a : X ↦ a = x) = {x} := by
    ext a
    simp [eq_comm]
  rw [hfilter]
  simp

/-- An injective reindexing has zero coefficient away from its image. -/
public theorem stdSimplex_map_apply_eq_zero_of_not_mem_range
    {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (w : stdSimplex ℝ X) (y : Y)
    (hy : y ∉ Set.range f) :
    stdSimplex.map f w y = 0 := by
  classical
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro x hx
  exact (hy ⟨x, (Finset.mem_filter.mp hx).2⟩).elim

/-- Mapping a standard simplex commutes with taking a finite affine combination. -/
public theorem stdSimplex_map_affineCombination
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (f : Y → Z) (p : X → stdSimplex ℝ Y) (w : stdSimplex ℝ X) :
    stdSimplex.map f (stdSimplexAffineCombination p w) =
      stdSimplexAffineCombination (fun x ↦ stdSimplex.map f (p x)) w := by
  classical
  ext z
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    stdSimplexAffineCombination_apply]
  change (Finset.univ.filter (fun y ↦ f y = z)).sum
      (fun y ↦ ∑ x, w x * p x y) =
    ∑ x, w x * (Finset.univ.filter (fun y ↦ f y = z)).sum (fun y ↦ p x y)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The barycenter of a nonempty face of the standard `n`-simplex, embedded in the ambient
standard simplex. -/
public noncomputable def nonemptyFiniteChainBarycenter {n : ℕ}
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) :
    stdSimplex ℝ (Fin (n + 1)) := by
  haveI : Nonempty A.finset := A.nonempty.to_subtype
  exact stdSimplex.map (fun a : A.finset ↦ a.1.down)
    (stdSimplex.barycenter : stdSimplex ℝ A.finset)

set_option linter.style.haveILetI false in
/-- Coordinate formula for the barycenter of a face. -/
@[simp]
public theorem nonemptyFiniteChainBarycenter_apply {n : ℕ}
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1))))
    (i : Fin (n + 1)) :
    nonemptyFiniteChainBarycenter A i =
      if ULift.up i ∈ A.finset then (A.finset.card : ℝ)⁻¹ else 0 := by
  classical
  letI : Nonempty A.finset := A.nonempty.to_subtype
  unfold nonemptyFiniteChainBarycenter
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  by_cases hi : ULift.up i ∈ A.finset
  · rw [if_pos hi]
    have hfilter :
        Finset.univ.filter (fun a : A.finset ↦ a.1.down = i) =
          {(⟨ULift.up i, hi⟩ : A.finset)} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · exact fun ha ↦ Subtype.ext (ULift.ext _ _ ha)
      · rintro rfl
        rfl
    rw [hfilter]
    simp only [Finset.sum_singleton]
    change (stdSimplex.barycenter : stdSimplex ℝ A.finset).val _ = _
    rw [stdSimplex.barycenter_apply, Fintype.card_coe]
  · rw [if_neg hi]
    have hfilter :
        Finset.univ.filter (fun a : A.finset ↦ a.1.down = i) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro a _ ha
      apply hi
      have haup : a.1 = ULift.up i := ULift.ext _ _ ha
      simpa [haup] using a.2
    rw [hfilter]
    simp

/-- The order embedding of vertices associated to a standard-simplex face inclusion. -/
public def standardSimplexFaceVertexOrderHom
    (n : ℕ) (p : Fin (n + 2)) :
    ULift.{0} (Fin (n + 1)) →o ULift.{0} (Fin (n + 2)) where
  toFun a := ULift.up (p.succAbove a.down)
  monotone' _ _ h := (Fin.strictMono_succAbove p).monotone h

/-- The explicit face vertex embedding is the vertex map used by `SimplexCategory.sd`. -/
public theorem standardSimplexFaceVertexOrderHom_eq_toPartOrd
    (n : ℕ) (p : Fin (n + 2)) :
    standardSimplexFaceVertexOrderHom n p =
      (SimplexCategory.toPartOrd.{0}.map (SimplexCategory.δ p)).hom := by
  ext a
  induction a
  rfl

set_option linter.style.haveILetI false in
/-- Face inclusions send face barycenters to the corresponding ambient face barycenters. -/
public theorem nonemptyFiniteChainBarycenter_face
    (n : ℕ) (p : Fin (n + 2))
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) :
    nonemptyFiniteChainBarycenter
        (A.map (standardSimplexFaceVertexOrderHom n p)) =
      stdSimplex.map p.succAbove (nonemptyFiniteChainBarycenter A) := by
  classical
  let g := standardSimplexFaceVertexOrderHom n p
  change nonemptyFiniteChainBarycenter (A.map g) =
    stdSimplex.map p.succAbove (nonemptyFiniteChainBarycenter A)
  have hg (a : ULift.{0} (Fin (n + 1))) :
      g a = ULift.up (p.succAbove a.down) := by
    induction a
    rfl
  have hginj : Function.Injective g := by
    intro a b hab
    rw [hg a, hg b] at hab
    exact ULift.down_injective (Fin.succAbove_right_injective (congrArg ULift.down hab))
  have hcard : (A.map g).finset.card = A.finset.card := by
    letI : DecidableEq (ULift.{0} (Fin (n + 2))) := Classical.decEq _
    unfold NonemptyFiniteChains.map
    exact Finset.card_image_of_injective A.finset hginj
  ext y
  by_cases hy : y ∈ Set.range p.succAbove
  · obtain ⟨x, rfl⟩ := hy
    have hmem :
        ULift.up (p.succAbove x) ∈ (A.map g).finset ↔
          ULift.up x ∈ A.finset := by
      rw [NonemptyFiniteChains.mem_map_iff]
      constructor
      · rintro ⟨a, ha, hga⟩
        rw [hg a] at hga
        have haeq : a = ULift.up x := ULift.ext _ _
          (Fin.succAbove_right_injective (ULift.up_injective hga))
        simpa [haeq] using ha
      · intro hx
        exact ⟨ULift.up x, hx, by simp [hg]⟩
    rw [stdSimplex_map_apply_injective p.succAbove Fin.succAbove_right_injective,
      nonemptyFiniteChainBarycenter_apply, nonemptyFiniteChainBarycenter_apply]
    by_cases hx : ULift.up x ∈ A.finset
    · simp [hx, hmem.mpr hx, hcard]
    · have hx' : ULift.up (p.succAbove x) ∉ (A.map g).finset :=
        fun h ↦ hx (hmem.mp h)
      simp [hx, hx']
  · rw [stdSimplex_map_apply_eq_zero_of_not_mem_range p.succAbove _ y hy,
      nonemptyFiniteChainBarycenter_apply, if_neg]
    intro hmem
    rw [NonemptyFiniteChains.mem_map_iff] at hmem
    obtain ⟨a, _, hga⟩ := hmem
    rw [hg a] at hga
    exact hy ⟨a.down, ULift.up_injective hga⟩

/-- The affine map associated to a flag of nonempty faces. -/
public noncomputable def affineFlagContinuousMap (n k : ℕ)
    (F : ComposableArrows
      (NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) k) :
    C(stdSimplex ℝ (Fin (k + 1)), stdSimplex ℝ (Fin (n + 1))) :=
  ⟨stdSimplexAffineCombination
      (fun j ↦ nonemptyFiniteChainBarycenter (F.obj j)),
    continuous_stdSimplexAffineCombination _⟩

/-- The continuous affine inclusion of a codimension-one face of a standard simplex. -/
public noncomputable def standardSimplexFaceContinuousMap
    (n : ℕ) (p : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map p.succAbove, stdSimplex.continuous_map p.succAbove⟩

/-- Affine realization of flags is natural under ambient coface inclusions. -/
public theorem affineFlagContinuousMap_face
    (n k : ℕ) (p : Fin (n + 2))
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k))) :
    affineFlagContinuousMap (n + 1) k
        ((SimplexCategory.sd.{0}.map (SimplexCategory.δ p)).app _ F) =
      (standardSimplexFaceContinuousMap n p).comp
        (affineFlagContinuousMap n k F) := by
  apply ContinuousMap.ext
  intro w
  change stdSimplexAffineCombination
      (fun j ↦ nonemptyFiniteChainBarycenter
        (((SimplexCategory.sd.{0}.map (SimplexCategory.δ p)).app _ F).obj j)) w =
    stdSimplex.map p.succAbove
      (stdSimplexAffineCombination
        (fun j ↦ nonemptyFiniteChainBarycenter (F.obj j)) w)
  rw [stdSimplex_map_affineCombination]
  apply congrArg (fun q ↦ stdSimplexAffineCombination q w)
  funext j
  change nonemptyFiniteChainBarycenter
      ((F.obj j).map
        (SimplexCategory.toPartOrd.{0}.map (SimplexCategory.δ p)).hom) = _
  rw [← standardSimplexFaceVertexOrderHom_eq_toPartOrd]
  exact nonemptyFiniteChainBarycenter_face n p (F.obj j)

/-- The face inclusion as a morphism of topological spaces. -/
public noncomputable def standardSimplexFaceTopCatMap
    (n : ℕ) (p : Fin (n + 2)) :
    TopCat.of (stdSimplex ℝ (Fin (n + 1))) ⟶
      TopCat.of (stdSimplex ℝ (Fin (n + 2))) :=
  TopCat.ofHom (standardSimplexFaceContinuousMap n p)

/-- A flag in the barycentric subdivision nerve, regarded as an ordinary singular simplex of
the ambient topological standard simplex. -/
public noncomputable def affineFlagSingularSimplex (n k : ℕ)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k))) :
    (TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).obj
      (Opposite.op (SimplexCategory.mk k)) :=
  (TopCat.toSSetObjEquiv _ _).symm (affineFlagContinuousMap n k F)

/-- Under the continuous-map description of singular simplices, functoriality in the
topological space is postcomposition. -/
@[simp]
public theorem toSSetObjEquiv_map_apply
    {X Y : TopCat.{0}} (f : X ⟶ Y) {k : ℕ}
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk k)))
    (w : stdSimplex ℝ (Fin (k + 1))) :
    Y.toSSetObjEquiv _ ((TopCat.toSSet.map f).app _ x) w =
      f (X.toSSetObjEquiv _ x w) :=
  rfl

/-- Affine flag singular simplices commute with ambient coface inclusions. -/
public theorem affineFlagSingularSimplex_face
    (n k : ℕ) (p : Fin (n + 2))
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k))) :
    (TopCat.toSSet.map (standardSimplexFaceTopCatMap n p)).app _
        (affineFlagSingularSimplex n k F) =
      affineFlagSingularSimplex (n + 1) k
        ((SimplexCategory.sd.{0}.map (SimplexCategory.δ p)).app _ F) := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  apply ContinuousMap.ext
  intro w
  rw [toSSetObjEquiv_map_apply]
  change standardSimplexFaceContinuousMap n p
      (affineFlagContinuousMap n k F w) =
    affineFlagContinuousMap (n + 1) k
      ((SimplexCategory.sd.{0}.map (SimplexCategory.δ p)).app _ F) w
  rw [affineFlagContinuousMap_face]
  rfl

/-- Deleting a vertex of a flag agrees with restricting its affine singular simplex to the
corresponding face. -/
@[simp]
public theorem affineFlagSingularSimplex_delta
    (n k : ℕ) (i : Fin (k + 2))
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk (k + 1)))) :
    (TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).δ i
        (affineFlagSingularSimplex n (k + 1) F) =
      affineFlagSingularSimplex n k
        ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).δ i F) := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  apply ContinuousMap.ext
  intro w
  change stdSimplexAffineCombination
      (fun j ↦ nonemptyFiniteChainBarycenter (F.obj j))
        (stdSimplex.map i.succAbove w) =
    stdSimplexAffineCombination
      (fun j ↦ nonemptyFiniteChainBarycenter
        (((SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).δ i F).obj j)) w
  rw [stdSimplexAffineCombination_map]
  rfl

/-- The degree-`k` homomorphism which realizes every flag as its affine singular simplex. -/
public noncomputable def affineFlagChainComponent (n k : ℕ) :
    ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).chainComplex
        (AddCommGrpCat.of ℤ)).X k ⟶
      ((TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
        (AddCommGrpCat.of ℤ)).X k :=
  Sigma.desc (fun F ↦
    (TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).ιChainComplex
      (affineFlagSingularSimplex n k F))

@[reassoc (attr := simp)]
public theorem iota_affineFlagChainComponent
    (n k : ℕ)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k))) :
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).ιChainComplex F ≫
        affineFlagChainComponent n k =
      (TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).ιChainComplex
        (affineFlagSingularSimplex n k F) := by
  apply Sigma.ι_desc

/-- The affine flag realization commutes with the simplicial differentials. -/
public theorem affineFlagChainComponents_commute (n k : ℕ) :
    affineFlagChainComponent n (k + 1) ≫
        ((TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
            (AddCommGrpCat.of ℤ)).d (k + 1) k =
      ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).chainComplex
          (AddCommGrpCat.of ℤ)).d (k + 1) k ≫
        affineFlagChainComponent n k := by
  apply (SimplexCategory.sd.{0}.obj
    (SimplexCategory.mk n)).chainComplex_hom_ext
  intro F
  rw [← Category.assoc, iota_affineFlagChainComponent, SSet.ιChainComplex_d,
    ← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, iota_affineFlagChainComponent,
    affineFlagSingularSimplex_delta]

/-- The all-degree affine realization from the barycentric nerve model to the ordinary singular
chain complex of the topological standard simplex. -/
public noncomputable def affineFlagChainMap (n : ℕ) :
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).chainComplex
        (AddCommGrpCat.of ℤ) ⟶
      (TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
        (AddCommGrpCat.of ℤ) :=
  ChainComplex.ofHom (affineFlagChainComponent n)
    (affineFlagChainComponents_commute n)

@[simp]
public theorem affineFlagChainMap_f (n k : ℕ) :
    (affineFlagChainMap n).f k = affineFlagChainComponent n k :=
  rfl

/-- The affine flag chain maps commute with ambient coface inclusions. -/
public theorem affineFlagChainMap_face
    (n : ℕ) (p : Fin (n + 2)) :
    affineFlagChainMap n ≫
        SSet.chainComplexMap
          (TopCat.toSSet.map (standardSimplexFaceTopCatMap n p))
          (AddCommGrpCat.of ℤ) =
      SSet.chainComplexMap
          (SimplexCategory.sd.{0}.map (SimplexCategory.δ p))
          (AddCommGrpCat.of ℤ) ≫
        affineFlagChainMap (n + 1) := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply (SimplexCategory.sd.{0}.obj
    (SimplexCategory.mk n)).chainComplex_hom_ext
  intro F
  change ((SimplexCategory.sd.{0}.obj
      (SimplexCategory.mk n)).ιChainComplex F ≫
        (affineFlagChainMap n).f k) ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map (standardSimplexFaceTopCatMap n p))
        (AddCommGrpCat.of ℤ)).f k =
    ((SimplexCategory.sd.{0}.obj
      (SimplexCategory.mk n)).ιChainComplex F ≫
        (SSet.chainComplexMap
          (SimplexCategory.sd.{0}.map (SimplexCategory.δ p))
          (AddCommGrpCat.of ℤ)).f k) ≫
      (affineFlagChainMap (n + 1)).f k
  simp only [affineFlagChainMap_f]
  rw [iota_affineFlagChainComponent, SSet.ι_chainComplexMap_f,
    affineFlagSingularSimplex_face, SSet.ι_chainComplexMap_f,
    iota_affineFlagChainComponent]

/-- The signed affine barycentric subdivision of the topological standard `n`-simplex, now as
an actual integral singular chain. -/
public noncomputable def affineSubdividedSimplexFundamentalChain (n : ℕ) :
    AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
        (AddCommGrpCat.of ℤ)).X n :=
  subdividedSimplexFundamentalChain n ≫ (affineFlagChainMap n).f n

/-- Realizing a subdivided face in its ambient simplex agrees with first realizing the face and
then applying the topological coface inclusion. -/
public theorem affineSubdividedSimplexFundamentalChain_face
    (n : ℕ) (p : Fin (n + 2)) :
    affineSubdividedSimplexFundamentalChain n ≫
        (SSet.chainComplexMap
          (TopCat.toSSet.map (standardSimplexFaceTopCatMap n p))
          (AddCommGrpCat.of ℤ)).f n =
      (subdividedSimplexFundamentalChain n ≫
        (SSet.chainComplexMap
          (SimplexCategory.sd.{0}.map (SimplexCategory.δ p))
          (AddCommGrpCat.of ℤ)).f n) ≫
        (affineFlagChainMap (n + 1)).f n := by
  have h := congrArg (fun F ↦ F.f n) (affineFlagChainMap_face n p)
  change (affineFlagChainMap n).f n ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map (standardSimplexFaceTopCatMap n p))
        (AddCommGrpCat.of ℤ)).f n =
    (SSet.chainComplexMap
      (SimplexCategory.sd.{0}.map (SimplexCategory.δ p))
      (AddCommGrpCat.of ℤ)).f n ≫
      (affineFlagChainMap (n + 1)).f n at h
  rw [affineSubdividedSimplexFundamentalChain, Category.assoc, h, ← Category.assoc]

/-- The realized alternating boundary chain: each subdivided face flag is interpreted inside
the ambient topological `(n+1)`-simplex. -/
public noncomputable def affineSubdividedSimplexAlternatingFaceChain (n : ℕ) :
    AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).chainComplex
        (AddCommGrpCat.of ℤ)).X n :=
  subdividedSimplexAlternatingFaceChain n ≫ (affineFlagChainMap (n + 1)).f n

/-- The alternating sum of the affine subdivided faces, each included into the ambient
topological standard simplex. -/
public noncomputable def affineSubdividedSimplexExpectedBoundaryChain (n : ℕ) :
    AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).chainComplex
        (AddCommGrpCat.of ℤ)).X n :=
  ∑ p : Fin (n + 2), (-1 : ℤ) ^ p.val •
    (affineSubdividedSimplexFundamentalChain n ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map (standardSimplexFaceTopCatMap n p))
        (AddCommGrpCat.of ℤ)).f n)

/-- The model alternating face chain realizes to the geometric alternating face chain. -/
public theorem affineSubdividedSimplexAlternatingFaceChain_eq_expected
    (n : ℕ) :
    affineSubdividedSimplexAlternatingFaceChain n =
      affineSubdividedSimplexExpectedBoundaryChain n := by
  rw [affineSubdividedSimplexAlternatingFaceChain, subdividedSimplexAlternatingFaceChain,
    Preadditive.sum_comp, affineSubdividedSimplexExpectedBoundaryChain]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Preadditive.zsmul_comp, Category.assoc]
  apply congrArg (fun f ↦ ((-1 : ℤ) ^ p.val) • f)
  exact (affineSubdividedSimplexFundamentalChain_face n p).symm

/-- The affine barycentric fundamental chain has exactly the expected alternating boundary in
ordinary singular chains. -/
public theorem affineSubdividedSimplexFundamentalChain_boundary (n : ℕ) :
    affineSubdividedSimplexFundamentalChain (n + 1) ≫
        ((TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 1) n =
      affineSubdividedSimplexAlternatingFaceChain n := by
  let F := affineFlagChainMap (n + 1)
  change (subdividedSimplexFundamentalChain (n + 1) ≫ F.f (n + 1)) ≫ _ = _
  calc
    _ = subdividedSimplexFundamentalChain (n + 1) ≫
        (F.f (n + 1) ≫ _) := Category.assoc _ _ _
    _ = subdividedSimplexFundamentalChain (n + 1) ≫
        (_ ≫ F.f n) := by rw [F.comm]
    _ = (subdividedSimplexFundamentalChain (n + 1) ≫
        ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n) ≫ F.f n :=
      (Category.assoc _ _ _).symm
    _ = subdividedSimplexAlternatingFaceChain n ≫ F.f n := by
      rw [barycentricFundamentalBoundaryIdentity n]
    _ = _ := rfl

/-- Geometric form of the affine subdivision boundary theorem. -/
public theorem affineSubdividedSimplexFundamentalChain_boundary_expected
    (n : ℕ) :
    affineSubdividedSimplexFundamentalChain (n + 1) ≫
        ((TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 1) n =
      affineSubdividedSimplexExpectedBoundaryChain n := by
  rw [affineSubdividedSimplexFundamentalChain_boundary,
    affineSubdividedSimplexAlternatingFaceChain_eq_expected]

/-- The topological map represented by a singular simplex. -/
public noncomputable def singularSimplexTopCatMap
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    TopCat.of (stdSimplex ℝ (Fin (n + 1))) ⟶ X :=
  TopCat.ofHom (X.toSSetObjEquiv _ x)

/-- The map represented by a face of a singular simplex is obtained by precomposing with the
standard topological coface inclusion. -/
public theorem singularSimplexTopCatMap_delta
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk (n + 1))))
    (p : Fin (n + 2)) :
    standardSimplexFaceTopCatMap n p ≫
        singularSimplexTopCatMap X (n + 1) x =
      singularSimplexTopCatMap X n ((TopCat.toSSet.obj X).δ p x) := by
  ext w
  rfl

/-- Mapping a singular simplex postcomposes its represented topological map. -/
public theorem singularSimplexTopCatMap_map
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    singularSimplexTopCatMap Y n ((TopCat.toSSet.map f).app _ x) =
      singularSimplexTopCatMap X n x ≫ f := by
  ext w
  rfl

/-- The affine barycentric subdivision chain associated to one singular simplex. -/
public noncomputable def affineSubdivisionSingularSimplexChain
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)).X n :=
  affineSubdividedSimplexFundamentalChain n ≫
    (SSet.chainComplexMap
      (TopCat.toSSet.map (singularSimplexTopCatMap X n x))
      (AddCommGrpCat.of ℤ)).f n

/-- Subdivision of a single singular simplex is natural in the target space. -/
public theorem affineSubdivisionSingularSimplexChain_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    affineSubdivisionSingularSimplexChain Y n
        ((TopCat.toSSet.map f).app _ x) =
      affineSubdivisionSingularSimplexChain X n x ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f)
          (AddCommGrpCat.of ℤ)).f n := by
  let G := (SSet.chainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)
  have hsset :
      TopCat.toSSet.map (singularSimplexTopCatMap X n x) ≫
          TopCat.toSSet.map f =
        TopCat.toSSet.map
          (singularSimplexTopCatMap Y n
            ((TopCat.toSSet.map f).app _ x)) := by
    rw [← Functor.map_comp, ← singularSimplexTopCatMap_map]
  have hmap := G.congr_map hsset
  rw [Functor.map_comp] at hmap
  have hn := congrArg (fun K ↦ K.f n) hmap
  change affineSubdividedSimplexFundamentalChain n ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map
          (singularSimplexTopCatMap Y n
            ((TopCat.toSSet.map f).app _ x)))
        (AddCommGrpCat.of ℤ)).f n =
    (affineSubdividedSimplexFundamentalChain n ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map (singularSimplexTopCatMap X n x))
        (AddCommGrpCat.of ℤ)).f n) ≫
      (SSet.chainComplexMap (TopCat.toSSet.map f)
        (AddCommGrpCat.of ℤ)).f n
  rw [Category.assoc]
  change _ = affineSubdividedSimplexFundamentalChain n ≫
    ((G.map (TopCat.toSSet.map (singularSimplexTopCatMap X n x))).f n ≫
      (G.map (TopCat.toSSet.map f)).f n)
  change (G.map (TopCat.toSSet.map (singularSimplexTopCatMap X n x))).f n ≫
      (G.map (TopCat.toSSet.map f)).f n = _ at hn
  rw [hn]

/-- The alternating sum of the affine subdivisions of the faces of a singular simplex. -/
public noncomputable def affineSubdivisionSingularSimplexAlternatingFaceChain
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk (n + 1)))) :
    AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)).X n :=
  ∑ p : Fin (n + 2), (-1 : ℤ) ^ p.val •
    affineSubdivisionSingularSimplexChain X n
      ((TopCat.toSSet.obj X).δ p x)

/-- The affine subdivision of one singular simplex has the alternating sum of the subdivisions
of its faces as boundary. -/
public theorem affineSubdivisionSingularSimplexChain_boundary
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk (n + 1)))) :
    affineSubdivisionSingularSimplexChain X (n + 1) x ≫
        ((TopCat.toSSet.obj X).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n =
      affineSubdivisionSingularSimplexAlternatingFaceChain X n x := by
  let F := SSet.chainComplexMap
    (TopCat.toSSet.map (singularSimplexTopCatMap X (n + 1) x))
    (AddCommGrpCat.of ℤ)
  change (affineSubdividedSimplexFundamentalChain (n + 1) ≫
    F.f (n + 1)) ≫ _ = _
  calc
    _ = affineSubdividedSimplexFundamentalChain (n + 1) ≫
        (F.f (n + 1) ≫ _) := Category.assoc _ _ _
    _ = affineSubdividedSimplexFundamentalChain (n + 1) ≫
        (_ ≫ F.f n) := by rw [F.comm]
    _ = (affineSubdividedSimplexFundamentalChain (n + 1) ≫
        ((TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 1) n) ≫ F.f n :=
      (Category.assoc _ _ _).symm
    _ = affineSubdividedSimplexExpectedBoundaryChain n ≫ F.f n := by
      rw [affineSubdividedSimplexFundamentalChain_boundary_expected]
    _ = affineSubdivisionSingularSimplexAlternatingFaceChain X n x := by
      rw [affineSubdividedSimplexExpectedBoundaryChain,
        Preadditive.sum_comp,
        affineSubdivisionSingularSimplexAlternatingFaceChain]
      apply Finset.sum_congr rfl
      intro p _
      simp only [Preadditive.zsmul_comp, Category.assoc]
      apply congrArg (fun f ↦ ((-1 : ℤ) ^ p.val) • f)
      let G := (SSet.chainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)
      have hsset :
          TopCat.toSSet.map (standardSimplexFaceTopCatMap n p) ≫
              TopCat.toSSet.map
                (singularSimplexTopCatMap X (n + 1) x) =
            TopCat.toSSet.map
              (singularSimplexTopCatMap X n
                ((TopCat.toSSet.obj X).δ p x)) := by
        rw [← Functor.map_comp, singularSimplexTopCatMap_delta]
      have hmap := G.congr_map hsset
      rw [Functor.map_comp] at hmap
      have hn := congrArg (fun K ↦ K.f n) hmap
      change (SSet.chainComplexMap
          (TopCat.toSSet.map (standardSimplexFaceTopCatMap n p))
          (AddCommGrpCat.of ℤ)).f n ≫ F.f n =
        (SSet.chainComplexMap
          (TopCat.toSSet.map
            (singularSimplexTopCatMap X n
              ((TopCat.toSSet.obj X).δ p x)))
          (AddCommGrpCat.of ℤ)).f n at hn
      rw [affineSubdivisionSingularSimplexChain, hn]

/-- The degreewise affine barycentric subdivision operator on integral singular chains. -/
public noncomputable def affineSingularSubdivisionComponent
    (X : TopCat.{0}) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)).X n :=
  Sigma.desc (affineSubdivisionSingularSimplexChain X n)

@[reassoc (attr := simp)]
public theorem iota_affineSingularSubdivisionComponent
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj X).ιChainComplex x ≫
        affineSingularSubdivisionComponent X n =
      affineSubdivisionSingularSimplexChain X n x := by
  apply Sigma.ι_desc

/-- The degreewise affine singular subdivision operators are natural. -/
public theorem affineSingularSubdivisionComponent_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (SSet.chainComplexMap (TopCat.toSSet.map f)
        (AddCommGrpCat.of ℤ)).f n ≫
      affineSingularSubdivisionComponent Y n =
    affineSingularSubdivisionComponent X n ≫
      (SSet.chainComplexMap (TopCat.toSSet.map f)
        (AddCommGrpCat.of ℤ)).f n := by
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro x
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, iota_affineSingularSubdivisionComponent,
    ← Category.assoc, iota_affineSingularSubdivisionComponent,
    affineSubdivisionSingularSimplexChain_naturality]

/-- The affine singular subdivision components commute with the boundary maps. -/
public theorem affineSingularSubdivisionComponents_commute
    (X : TopCat.{0}) (n : ℕ) :
    affineSingularSubdivisionComponent X (n + 1) ≫
        ((TopCat.toSSet.obj X).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n =
      ((TopCat.toSSet.obj X).chainComplex
        (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
        affineSingularSubdivisionComponent X n := by
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro x
  rw [← Category.assoc, iota_affineSingularSubdivisionComponent,
    affineSubdivisionSingularSimplexChain_boundary, ← Category.assoc,
    SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp,
    iota_affineSingularSubdivisionComponent]
  rfl

/-- The genuine affine barycentric subdivision endomorphism of the integral singular chain
complex of a topological space. -/
public noncomputable def affineSingularSubdivisionChainMap
    (X : TopCat.{0}) :
    (TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ) ⟶
      (TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ) :=
  ChainComplex.ofHom (affineSingularSubdivisionComponent X)
    (affineSingularSubdivisionComponents_commute X)

@[simp]
public theorem affineSingularSubdivisionChainMap_f
    (X : TopCat.{0}) (n : ℕ) :
    (affineSingularSubdivisionChainMap X).f n =
      affineSingularSubdivisionComponent X n :=
  rfl

/-- The affine singular subdivision chain endomorphisms are natural in continuous maps. -/
public theorem affineSingularSubdivisionChainMap_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) :
    SSet.chainComplexMap (TopCat.toSSet.map f)
        (AddCommGrpCat.of ℤ) ≫
      affineSingularSubdivisionChainMap Y =
    affineSingularSubdivisionChainMap X ≫
      SSet.chainComplexMap (TopCat.toSSet.map f)
        (AddCommGrpCat.of ℤ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact affineSingularSubdivisionComponent_naturality f n

end AlgebraicTopology.Singular
