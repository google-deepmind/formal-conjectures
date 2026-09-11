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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularAffineSubdivision
public import Mathlib.Topology.Homotopy.Contractible

import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Logic.Equiv.PartialEquiv

/-!
This module is ported from Paul Lezeau's corresponding file in
`sphere-six-complex` pull request #49, under the Apache-2.0 license.

# A universal prism for affine singular subdivision

The singular chain complex of every topological standard simplex is exact in positive degrees.
This supplies fillers for the universal subdivision discrepancies and hence the acyclic-models
prism between affine barycentric subdivision and the identity.  The first part of this file
establishes the exactness and packages a selected filler for every positive-degree cycle.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits ContinuousMap Set

namespace AlgebraicTopology.Singular

/-- Integral singular homology with coefficients in `ℤ`. -/
abbrev IntegralSingularHomology (k : ℕ) (X : Type) [TopologicalSpace X] : Type :=
  (singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ) |>.obj (TopCat.of X)

/-- Integral singular homology is invariant under a homotopy equivalence. -/
noncomputable def integralSingularHomologyEquivOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (k : ℕ) (e : X ≃ₕ Y) :
    IntegralSingularHomology k X ≃+ IntegralSingularHomology k Y := by
  let F := (singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  let i : F.obj (TopCat.of X) ≅ F.obj (TopCat.of Y) :=
    CategoryTheory.Iso.mk (F.map f) (F.map g) (by
      rw [← F.map_comp, ← F.map_id]
      exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
        e.left_inv.some (AddCommGrpCat.of ℤ) k) (by
      rw [← F.map_comp, ← F.map_id]
      exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
        e.right_inv.some (AddCommGrpCat.of ℤ) k)
  exact i.addCommGroupIsoToAddEquiv

/-- A real topological standard simplex is contractible because it is nonempty and convex. -/
public theorem standardTopologicalSimplex_contractibleSpace (m : ℕ) :
    ContractibleSpace (stdSimplex ℝ (Fin (m + 1))) :=
  (convex_stdSimplex ℝ (Fin (m + 1))).contractibleSpace
    ⟨stdSimplex.vertex 0, stdSimplex.vertex 0 |>.2⟩

/-- Positive-degree integral singular homology of a topological standard simplex vanishes. -/
public theorem standardTopologicalSimplex_integralSingularHomology_isZero
    (m k : ℕ) (hk : k ≠ 0) :
    IsZero (((TopCat.toSSet.obj
      (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
        (AddCommGrpCat.of ℤ)).homology k) := by
  change IsZero (((singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)).obj
      (TopCat.of (stdSimplex ℝ (Fin (m + 1)))))
  let : ContractibleSpace (stdSimplex ℝ (Fin (m + 1))) :=
    standardTopologicalSimplex_contractibleSpace m
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit
    (stdSimplex ℝ (Fin (m + 1)))
  have hunit :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      AddCommGrpCat k (AddCommGrpCat.of ℤ) (TopCat.of Unit) hk
  let : Subsingleton (IntegralSingularHomology k Unit) :=
    AddCommGrpCat.subsingleton_of_isZero hunit
  let he := integralSingularHomologyEquivOfHomotopyEquiv k e
  let : Subsingleton
      (IntegralSingularHomology k (stdSimplex ℝ (Fin (m + 1)))) :=
    ⟨fun x y ↦ he.injective (Subsingleton.elim _ _)⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- The singular chain complex of a standard simplex is exact in every positive degree. -/
public theorem standardTopologicalSimplex_singularChainExactAt
    (m k : ℕ) (hk : k ≠ 0) :
    ((TopCat.toSSet.obj
      (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
        (AddCommGrpCat.of ℤ)).ExactAt k := by
  let K := (TopCat.toSSet.obj
    (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
      (AddCommGrpCat.of ℤ)
  rw [K.exactAt_iff_isZero_homology]
  exact standardTopologicalSimplex_integralSingularHomology_isZero m k hk

/-- Every positive-degree cycle in a topological standard simplex bounds.  This is stated for
morphisms from `ℤ`, matching the chain representation used throughout the subdivision files. -/
public theorem exists_standardTopologicalSimplex_cycleFiller
    (m n : ℕ)
    (z : AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 1))
    (hz : z ≫
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n = 0) :
    ∃ p : AddCommGrpCat.of ℤ ⟶
        ((TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
            (AddCommGrpCat.of ℤ)).X (n + 2),
      p ≫
        ((TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) = z := by
  let K := (TopCat.toSSet.obj
    (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
      (AddCommGrpCat.of ℤ)
  have hexact : (K.sc' (n + 2) (n + 1) n).Exact :=
    (K.exactAt_iff' (i := n + 2) (j := n + 1) (k := n)
      (by simp) (by simp)).mp
        (standardTopologicalSimplex_singularChainExactAt m (n + 1)
          (by lia))
  have hz1 : K.d (n + 1) n (z 1) = 0 := by
    simpa using CategoryTheory.congr_fun hz 1
  obtain ⟨p, hp⟩ := (ShortComplex.ab_exact_iff _).mp hexact (z 1) hz1
  change K.X (n + 2) at p
  change K.d (n + 2) (n + 1) p = z 1 at hp
  refine ⟨AddCommGrpCat.asHom p, ?_⟩
  apply AddCommGrpCat.int_hom_ext
  change K.d (n + 2) (n + 1) ((AddCommGrpCat.asHom p) 1) = z 1
  rw [AddCommGrpCat.asHom_hom_apply, one_zsmul]
  exact hp

/-- A selected filler of a positive-degree cycle in a topological standard simplex. -/
public noncomputable def standardTopologicalSimplexCycleFiller
    (m n : ℕ)
    (z : AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 1))
    (hz : z ≫
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n = 0) :
    AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 2) :=
  (exists_standardTopologicalSimplex_cycleFiller m n z hz).choose

/-- The selected filler has the prescribed boundary. -/
public theorem standardTopologicalSimplexCycleFiller_boundary
    (m n : ℕ)
    (z : AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 1))
    (hz : z ≫
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n = 0) :
    standardTopologicalSimplexCycleFiller m n z hz ≫
        ((TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) = z :=
  (exists_standardTopologicalSimplex_cycleFiller m n z hz).choose_spec

/-- A total version of the positive-degree filler.  It is the selected filler when its input
is a cycle and zero otherwise; this form can be used in a structurally recursive definition
before the cycle condition has been proved. -/
public noncomputable def standardTopologicalSimplexTotalCycleFiller
    (m n : ℕ)
    (z : AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 1)) :
    AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 2) := by
  classical
  exact if hz : z ≫
        ((TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 1) n = 0 then
      standardTopologicalSimplexCycleFiller m n z hz
    else 0

/-- The total filler has the prescribed boundary whenever its input is a cycle. -/
public theorem standardTopologicalSimplexTotalCycleFiller_boundary
    (m n : ℕ)
    (z : AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 1))
    (hz : z ≫
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n = 0) :
    standardTopologicalSimplexTotalCycleFiller m n z ≫
        ((TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (m + 1))))).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) = z := by
  rw [standardTopologicalSimplexTotalCycleFiller, dif_pos hz]
  exact standardTopologicalSimplexCycleFiller_boundary m n z hz

/-- The identity map of the topological standard simplex, regarded as its universal singular
simplex. -/
public noncomputable def standardTopologicalSimplexIdentitySimplex (n : ℕ) :
    (TopCat.toSSet.obj
      (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).obj
        (Opposite.op (SimplexCategory.mk n)) :=
  (TopCat.toSSetObjEquiv _ _).symm (ContinuousMap.id _)

/-- Mapping the universal identity simplex along the map represented by a singular simplex
recovers that singular simplex. -/
@[simp]
public theorem standardTopologicalSimplexIdentitySimplex_map
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSet.map (singularSimplexTopCatMap X n x)).app _
        (standardTopologicalSimplexIdentitySimplex n) = x := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext w
  rfl

/-- Affine singular subdivision minus the identity, as a natural chain endomorphism. -/
public noncomputable def affineSingularSubdivisionDiscrepancyChainMap
    (X : TopCat.{0}) :
    (TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ) ⟶
      (TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ) :=
  affineSingularSubdivisionChainMap X - 𝟙 _

/-- The universal degree-`n` affine-subdivision discrepancy on the topological standard
`n`-simplex. -/
public noncomputable def standardAffineSubdivisionDiscrepancy (n : ℕ) :
    AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).X n :=
  (TopCat.toSSet.obj
      (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).ιChainComplex
        (standardTopologicalSimplexIdentitySimplex n) ≫
    (affineSingularSubdivisionDiscrepancyChainMap
      (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).f n

/-- Evaluating the discrepancy on a singular simplex transports the universal discrepancy
along the continuous map represented by that simplex. -/
public theorem iota_affineSingularSubdivisionDiscrepancyChainMap
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj X).ιChainComplex x ≫
        (affineSingularSubdivisionDiscrepancyChainMap X).f n =
      standardAffineSubdivisionDiscrepancy n ≫
        (SSet.chainComplexMap
          (TopCat.toSSet.map (singularSimplexTopCatMap X n x))
          (AddCommGrpCat.of ℤ)).f n := by
  unfold standardAffineSubdivisionDiscrepancy
  change (TopCat.toSSet.obj X).ιChainComplex x ≫
        ((affineSingularSubdivisionChainMap X).f n - 𝟙 _) =
      ((TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).ιChainComplex
            (standardTopologicalSimplexIdentitySimplex n) ≫
          ((affineSingularSubdivisionChainMap
            (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).f n - 𝟙 _)) ≫
        (SSet.chainComplexMap
          (TopCat.toSSet.map (singularSimplexTopCatMap X n x))
          (AddCommGrpCat.of ℤ)).f n
  simp only [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp]
  let F := SSet.chainComplexMap
    (TopCat.toSSet.map (singularSimplexTopCatMap X n x))
    (AddCommGrpCat.of ℤ)
  have htop :
      (TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).ιChainComplex
            (standardTopologicalSimplexIdentitySimplex n) ≫ F.f n =
        (TopCat.toSSet.obj X).ιChainComplex x := by
    dsimp [F]
    rw [SSet.ι_chainComplexMap_f,
      standardTopologicalSimplexIdentitySimplex_map]
  have hnat := congrArg (fun K ↦ K.f n)
    (affineSingularSubdivisionChainMap_naturality
      (singularSimplexTopCatMap X n x))
  change F.f n ≫ (affineSingularSubdivisionChainMap X).f n =
    (affineSingularSubdivisionChainMap
      (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).f n ≫ F.f n at hnat
  have hA :
      (TopCat.toSSet.obj X).ιChainComplex x ≫
          (affineSingularSubdivisionChainMap X).f n =
        ((TopCat.toSSet.obj
            (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).ιChainComplex
              (standardTopologicalSimplexIdentitySimplex n) ≫
            (affineSingularSubdivisionChainMap
              (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).f n) ≫ F.f n := by
    rw [← htop, Category.assoc, hnat, ← Category.assoc]
  change _ = _ - _
  rw [hA, htop]

/-- Affine subdivision fixes every singular zero-simplex. -/
public theorem affineSubdivisionSingularSimplexChain_zero
    (X : TopCat.{0})
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk 0))) :
    affineSubdivisionSingularSimplexChain X 0 x =
      (TopCat.toSSet.obj X).ιChainComplex x := by
  rw [affineSubdivisionSingularSimplexChain,
    affineSubdividedSimplexFundamentalChain,
    subdividedSimplexFundamentalChain]
  classical
  have hperm : (Finset.univ : Finset (Equiv.Perm (Fin 1))) = {1} := by
    ext σ
    simp [Subsingleton.elim σ 1]
  rw [hperm, Finset.sum_singleton]
  simp only [permutationSignInteger, Equiv.Perm.sign_one, Units.val_one,
    one_zsmul, affineFlagChainMap_f]
  rw [iota_affineFlagChainComponent, SSet.ι_chainComplexMap_f]
  congr 1
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext w
  rw [toSSetObjEquiv_map_apply]
  change X.toSSetObjEquiv _ x
      (affineFlagContinuousMap 0 0 (permutationMaximalFlagSimplex 1) w) =
    X.toSSetObjEquiv _ x w
  rw [Subsingleton.elim
    (affineFlagContinuousMap 0 0 (permutationMaximalFlagSimplex 1) w) w]

/-- The universal affine-subdivision discrepancy vanishes in degree zero. -/
@[simp]
public theorem standardAffineSubdivisionDiscrepancy_zero :
    standardAffineSubdivisionDiscrepancy 0 = 0 := by
  rw [standardAffineSubdivisionDiscrepancy,
    affineSingularSubdivisionDiscrepancyChainMap]
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f,
    Preadditive.comp_sub, Category.comp_id]
  rw [affineSingularSubdivisionChainMap_f,
    iota_affineSingularSubdivisionComponent,
    affineSubdivisionSingularSimplexChain_zero]
  exact sub_self _

/-- The map represented by a face of the universal identity simplex is the standard affine
coface inclusion. -/
public theorem singularSimplexTopCatMap_identity_delta
    (n : ℕ) (p : Fin (n + 2)) :
    singularSimplexTopCatMap
        (TopCat.of (stdSimplex ℝ (Fin (n + 2)))) n
        ((TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).δ p
            (standardTopologicalSimplexIdentitySimplex (n + 1))) =
      standardSimplexFaceTopCatMap n p := by
  ext w
  rfl

/-- The boundary of the universal discrepancy is the alternating transport of the lower
dimensional universal discrepancy over all affine coface inclusions. -/
public theorem standardAffineSubdivisionDiscrepancy_boundary
    (n : ℕ) :
    standardAffineSubdivisionDiscrepancy (n + 1) ≫
        ((TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 1) n =
      ∑ p : Fin (n + 2), (-1 : ℤ) ^ p.val •
        (standardAffineSubdivisionDiscrepancy n ≫
          (SSet.chainComplexMap
            (TopCat.toSSet.map (standardSimplexFaceTopCatMap n p))
            (AddCommGrpCat.of ℤ)).f n) := by
  rw [standardAffineSubdivisionDiscrepancy, Category.assoc]
  rw [(affineSingularSubdivisionDiscrepancyChainMap
    (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).comm]
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro p _
  apply congrArg (fun k ↦ ((-1 : ℤ) ^ p.val) • k)
  rw [iota_affineSingularSubdivisionDiscrepancyChainMap,
    singularSimplexTopCatMap_identity_delta]

/-- Transport one universal degree-raising singular chain along every singular simplex of an
arbitrary topological space. -/
public noncomputable def universalAffinePrismComponent
    (n : ℕ)
    (p : AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 1))
    (X : TopCat.{0}) :
    ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)).X (n + 1) :=
  Sigma.desc (fun x ↦ p ≫
    (SSet.chainComplexMap
      (TopCat.toSSet.map (singularSimplexTopCatMap X n x))
      (AddCommGrpCat.of ℤ)).f (n + 1))

@[reassoc (attr := simp)]
public theorem iota_universalAffinePrismComponent
    (n : ℕ)
    (p : AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 1))
    (X : TopCat.{0})
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj X).ιChainComplex x ≫
        universalAffinePrismComponent n p X =
      p ≫ (SSet.chainComplexMap
        (TopCat.toSSet.map (singularSimplexTopCatMap X n x))
        (AddCommGrpCat.of ℤ)).f (n + 1) := by
  apply Sigma.ι_desc

/-- The raw sum of the already constructed prisms over the faces of a standard simplex. -/
public noncomputable def standardAffinePrismFaceChain
    (prism : ∀ n : ℕ, AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 1)) :
    ∀ n : ℕ, AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).X n
  | 0 => 0
  | n + 1 =>
      ∑ p : Fin (n + 2), (-1 : ℤ) ^ p.val •
        (prism n ≫
          (SSet.chainComplexMap
            (TopCat.toSSet.map (standardSimplexFaceTopCatMap n p))
            (AddCommGrpCat.of ℤ)).f (n + 1))

@[simp]
public theorem standardAffinePrismFaceChain_zero
    (prism : ∀ n : ℕ, AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 1)) :
    standardAffinePrismFaceChain prism 0 = 0 :=
  rfl

/-- The face-prism sum is the boundary of the universal identity simplex followed by the
transported lower-dimensional prism operator. -/
public theorem standardAffinePrismFaceChain_eq_identity_boundary_comp
    (prism : ∀ n : ℕ, AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 1))
    (n : ℕ) :
    standardAffinePrismFaceChain prism (n + 1) =
      (TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).ιChainComplex
          (standardTopologicalSimplexIdentitySimplex (n + 1)) ≫
        ((TopCat.toSSet.obj
          (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
        universalAffinePrismComponent n (prism n)
          (TopCat.of (stdSimplex ℝ (Fin (n + 2)))) := by
  rw [standardAffinePrismFaceChain, ← Category.assoc,
    SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp,
    iota_universalAffinePrismComponent]
  apply Finset.sum_congr rfl
  intro p _
  apply congrArg (fun k ↦ ((-1 : ℤ) ^ p.val) • k)
  rw [singularSimplexTopCatMap_identity_delta]

/-- Transporting the raw face-prism sum along a singular simplex is its source boundary
followed by the transported lower-dimensional prism operator. -/
public theorem standardAffinePrismFaceChain_transport_raw
    (prism : ∀ n : ℕ, AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 1))
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk (n + 1)))) :
    standardAffinePrismFaceChain prism (n + 1) ≫
        (SSet.chainComplexMap
          (TopCat.toSSet.map (singularSimplexTopCatMap X (n + 1) x))
          (AddCommGrpCat.of ℤ)).f (n + 1) =
      (TopCat.toSSet.obj X).ιChainComplex x ≫
        ((TopCat.toSSet.obj X).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
        universalAffinePrismComponent n (prism n) X := by
  rw [standardAffinePrismFaceChain, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, Category.assoc]
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp,
    iota_universalAffinePrismComponent]
  apply Finset.sum_congr rfl
  intro p _
  apply congrArg (fun k ↦ ((-1 : ℤ) ^ p.val) • k)
  let G := (SSet.chainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)
  have hsset :
      TopCat.toSSet.map (standardSimplexFaceTopCatMap n p) ≫
          TopCat.toSSet.map (singularSimplexTopCatMap X (n + 1) x) =
        TopCat.toSSet.map
          (singularSimplexTopCatMap X n ((TopCat.toSSet.obj X).δ p x)) := by
    rw [← Functor.map_comp, singularSimplexTopCatMap_delta]
  have hmap := G.congr_map hsset
  rw [Functor.map_comp] at hmap
  have hn := congrArg (fun K ↦ K.f (n + 1)) hmap
  change (SSet.chainComplexMap
        (TopCat.toSSet.map (standardSimplexFaceTopCatMap n p))
        (AddCommGrpCat.of ℤ)).f (n + 1) ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map (singularSimplexTopCatMap X (n + 1) x))
        (AddCommGrpCat.of ℤ)).f (n + 1) =
    (SSet.chainComplexMap
      (TopCat.toSSet.map
        (singularSimplexTopCatMap X n ((TopCat.toSSet.obj X).δ p x)))
      (AddCommGrpCat.of ℤ)).f (n + 1) at hn
  rw [hn]

/-- A universal prism equation induces the corresponding operator equation on every
topological space in that degree. -/
public theorem universalAffinePrismComponent_boundary_succ
    (prism : ∀ n : ℕ, AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 1))
    (n : ℕ)
    (h : standardAffineSubdivisionDiscrepancy (n + 1) =
      prism (n + 1) ≫
          ((TopCat.toSSet.obj
            (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).chainComplex
              (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) +
        standardAffinePrismFaceChain prism (n + 1))
    (X : TopCat.{0}) :
    (affineSingularSubdivisionDiscrepancyChainMap X).f (n + 1) =
      universalAffinePrismComponent (n + 1) (prism (n + 1)) X ≫
        ((TopCat.toSSet.obj X).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) +
      ((TopCat.toSSet.obj X).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
        universalAffinePrismComponent n (prism n) X := by
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro x
  simp only [Preadditive.comp_add]
  rw [iota_affineSingularSubdivisionDiscrepancyChainMap, h,
    Preadditive.add_comp]
  apply congrArg₂ (fun a b ↦ a + b)
  · rw [← Category.assoc, iota_universalAffinePrismComponent]
    simp only [Category.assoc]
    congr 1
    symm
    exact (SSet.chainComplexMap
      (TopCat.toSSet.map (singularSimplexTopCatMap X (n + 1) x))
      (AddCommGrpCat.of ℤ)).comm (n + 2) (n + 1)
  · exact standardAffinePrismFaceChain_transport_raw prism X n x

/-- Once the prism equation is known in degree `n+1`, the residual used to define the next
prism is a cycle.  The cancellation is the chain identity `∂² = 0`. -/
public theorem standardAffinePrismResidual_cycle_succ
    (prism : ∀ n : ℕ, AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 1))
    (n : ℕ)
    (h : standardAffineSubdivisionDiscrepancy (n + 1) =
      prism (n + 1) ≫
          ((TopCat.toSSet.obj
            (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).chainComplex
              (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) +
        standardAffinePrismFaceChain prism (n + 1)) :
    (standardAffineSubdivisionDiscrepancy (n + 2) -
        standardAffinePrismFaceChain prism (n + 2)) ≫
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 3))))).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) = 0 := by
  let X : TopCat := TopCat.of (stdSimplex ℝ (Fin (n + 3)))
  let K := affineSingularSubdivisionDiscrepancyChainMap X
  let U := universalAffinePrismComponent (n + 1) (prism (n + 1)) X
  let V := universalAffinePrismComponent n (prism n) X
  have hop := universalAffinePrismComponent_boundary_succ prism n h X
  have hU : U ≫
      ((TopCat.toSSet.obj X).chainComplex
        (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) =
      K.f (n + 1) -
        ((TopCat.toSSet.obj X).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n ≫ V := by
    dsimp [K, U, V] at hop ⊢
    rw [hop]
    abel
  rw [Preadditive.sub_comp]
  have hface : standardAffinePrismFaceChain prism (n + 2) ≫
      ((TopCat.toSSet.obj X).chainComplex
        (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) =
      standardAffineSubdivisionDiscrepancy (n + 2) ≫
        ((TopCat.toSSet.obj X).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) := by
    rw [standardAffinePrismFaceChain_eq_identity_boundary_comp]
    change (((TopCat.toSSet.obj X).ιChainComplex
          (standardTopologicalSimplexIdentitySimplex (n + 2)) ≫
        ((TopCat.toSSet.obj X).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1)) ≫ U) ≫
          ((TopCat.toSSet.obj X).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) = _
    rw [Category.assoc, hU, Preadditive.comp_sub]
    have hdd :
        ((TopCat.toSSet.obj X).ιChainComplex
            (standardTopologicalSimplexIdentitySimplex (n + 2)) ≫
          ((TopCat.toSSet.obj X).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1)) ≫
            ((TopCat.toSSet.obj X).chainComplex
              (AddCommGrpCat.of ℤ)).d (n + 1) n = 0 := by
      rw [Category.assoc,
        ((TopCat.toSSet.obj X).chainComplex
          (AddCommGrpCat.of ℤ)).d_comp_d, comp_zero]
    have hddV :
        ((TopCat.toSSet.obj X).ιChainComplex
            (standardTopologicalSimplexIdentitySimplex (n + 2)) ≫
          ((TopCat.toSSet.obj X).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1)) ≫
            ((TopCat.toSSet.obj X).chainComplex
              (AddCommGrpCat.of ℤ)).d (n + 1) n ≫ V = 0 := by
      rw [← Category.assoc, hdd, zero_comp]
    rw [hddV, sub_zero]
    rw [Category.assoc, ← K.comm]
    unfold standardAffineSubdivisionDiscrepancy
    dsimp [X, K]
    exact (Category.assoc _ _ _).symm
  rw [hface, sub_self]

/-- The universal affine prisms, defined recursively by filling the discrepancy left after
the already constructed face prisms. -/
public noncomputable def canonicalAffineSubdivisionPrism
    (n : ℕ) : AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 1) :=
  match n with
  | 0 => 0
  | n + 1 =>
      standardTopologicalSimplexTotalCycleFiller (n + 1) n
        (standardAffineSubdivisionDiscrepancy (n + 1) -
          ∑ p : Fin (n + 2), (-1 : ℤ) ^ p.val •
            (canonicalAffineSubdivisionPrism n ≫
              (SSet.chainComplexMap
                (TopCat.toSSet.map (standardSimplexFaceTopCatMap n p))
                (AddCommGrpCat.of ℤ)).f (n + 1)))
termination_by n

@[simp]
public theorem canonicalAffineSubdivisionPrism_zero :
    canonicalAffineSubdivisionPrism 0 = 0 := by
  simp [canonicalAffineSubdivisionPrism]

/-- The successor prism is the chosen filler of discrepancy minus the already constructed
face-prism sum. -/
public theorem canonicalAffineSubdivisionPrism_succ (n : ℕ) :
    canonicalAffineSubdivisionPrism (n + 1) =
      standardTopologicalSimplexTotalCycleFiller (n + 1) n
        (standardAffineSubdivisionDiscrepancy (n + 1) -
          standardAffinePrismFaceChain canonicalAffineSubdivisionPrism (n + 1)) := by
  simp [canonicalAffineSubdivisionPrism, standardAffinePrismFaceChain]

/-- The first recursive residual is a cycle; its degree-zero discrepancy and previous prism
both vanish. -/
public theorem canonicalAffineSubdivisionPrismResidual_cycle_one :
    (standardAffineSubdivisionDiscrepancy 1 -
        standardAffinePrismFaceChain canonicalAffineSubdivisionPrism 1) ≫
      ((TopCat.toSSet.obj
        (TopCat.of (stdSimplex ℝ (Fin 2)))).chainComplex
          (AddCommGrpCat.of ℤ)).d 1 0 = 0 := by
  rw [Preadditive.sub_comp,
    standardAffineSubdivisionDiscrepancy_boundary]
  simp [standardAffinePrismFaceChain]

/-- The recursively filled universal chains satisfy the complete prism equation in every
degree. -/
public theorem canonicalAffineSubdivisionPrism_boundary (n : ℕ) :
    standardAffineSubdivisionDiscrepancy n =
      canonicalAffineSubdivisionPrism n ≫
          ((TopCat.toSSet.obj
            (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).chainComplex
              (AddCommGrpCat.of ℤ)).d (n + 1) n +
        standardAffinePrismFaceChain canonicalAffineSubdivisionPrism n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hcycle :
          (standardAffineSubdivisionDiscrepancy (n + 1) -
              standardAffinePrismFaceChain canonicalAffineSubdivisionPrism (n + 1)) ≫
            ((TopCat.toSSet.obj
              (TopCat.of (stdSimplex ℝ (Fin (n + 2))))).chainComplex
                (AddCommGrpCat.of ℤ)).d (n + 1) n = 0 := by
        cases n with
        | zero =>
            exact canonicalAffineSubdivisionPrismResidual_cycle_one
        | succ k =>
            exact standardAffinePrismResidual_cycle_succ
              canonicalAffineSubdivisionPrism k ih
      have hfill := standardTopologicalSimplexTotalCycleFiller_boundary
        (n + 1) n
        (standardAffineSubdivisionDiscrepancy (n + 1) -
          standardAffinePrismFaceChain canonicalAffineSubdivisionPrism (n + 1))
        hcycle
      rw [canonicalAffineSubdivisionPrism_succ, hfill]
      abel

/-- The canonical universal prism transported to every singular simplex in degree `n`. -/
public noncomputable def affineSingularSubdivisionPrismComponent
    (X : TopCat.{0}) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)).X (n + 1) :=
  universalAffinePrismComponent n (canonicalAffineSubdivisionPrism n) X

@[reassoc (attr := simp)]
public theorem iota_affineSingularSubdivisionPrismComponent
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj X).ιChainComplex x ≫
        affineSingularSubdivisionPrismComponent X n =
      canonicalAffineSubdivisionPrism n ≫
        (SSet.chainComplexMap
          (TopCat.toSSet.map (singularSimplexTopCatMap X n x))
          (AddCommGrpCat.of ℤ)).f (n + 1) :=
  iota_universalAffinePrismComponent n (canonicalAffineSubdivisionPrism n) X x

/-- The canonical affine prism components are natural in continuous maps. -/
public theorem affineSingularSubdivisionPrismComponent_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (SSet.chainComplexMap (TopCat.toSSet.map f)
        (AddCommGrpCat.of ℤ)).f n ≫
      affineSingularSubdivisionPrismComponent Y n =
    affineSingularSubdivisionPrismComponent X n ≫
      (SSet.chainComplexMap (TopCat.toSSet.map f)
        (AddCommGrpCat.of ℤ)).f (n + 1) := by
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro x
  rw [← Category.assoc, SSet.ι_chainComplexMap_f,
    iota_affineSingularSubdivisionPrismComponent, ← Category.assoc,
    iota_affineSingularSubdivisionPrismComponent]
  let G := (SSet.chainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)
  have hsset :
      TopCat.toSSet.map (singularSimplexTopCatMap X n x) ≫
          TopCat.toSSet.map f =
        TopCat.toSSet.map
          (singularSimplexTopCatMap Y n ((TopCat.toSSet.map f).app _ x)) := by
    rw [← Functor.map_comp, ← singularSimplexTopCatMap_map]
  have hmap := G.congr_map hsset
  rw [Functor.map_comp] at hmap
  have hn := congrArg (fun K ↦ K.f (n + 1)) hmap
  change (SSet.chainComplexMap
      (TopCat.toSSet.map (singularSimplexTopCatMap X n x))
      (AddCommGrpCat.of ℤ)).f (n + 1) ≫
      (SSet.chainComplexMap (TopCat.toSSet.map f)
        (AddCommGrpCat.of ℤ)).f (n + 1) =
    (SSet.chainComplexMap
      (TopCat.toSSet.map
        (singularSimplexTopCatMap Y n ((TopCat.toSSet.map f).app _ x)))
      (AddCommGrpCat.of ℤ)).f (n + 1) at hn
  rw [Category.assoc, hn]

/-- In positive degrees the canonical transported prism satisfies the discrepancy equation. -/
public theorem affineSingularSubdivisionPrismComponent_discrepancy_succ
    (X : TopCat.{0}) (n : ℕ) :
    (affineSingularSubdivisionDiscrepancyChainMap X).f (n + 1) =
      affineSingularSubdivisionPrismComponent X (n + 1) ≫
        ((TopCat.toSSet.obj X).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) +
      ((TopCat.toSSet.obj X).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
        affineSingularSubdivisionPrismComponent X n := by
  simpa only [affineSingularSubdivisionPrismComponent] using
    universalAffinePrismComponent_boundary_succ
      canonicalAffineSubdivisionPrism n
        (canonicalAffineSubdivisionPrism_boundary (n + 1)) X

/-- In degree zero the canonical transported prism satisfies the discrepancy equation, with
no lower-dimensional face term. -/
public theorem affineSingularSubdivisionPrismComponent_discrepancy_zero
    (X : TopCat.{0}) :
    (affineSingularSubdivisionDiscrepancyChainMap X).f 0 =
      affineSingularSubdivisionPrismComponent X 0 ≫
        ((TopCat.toSSet.obj X).chainComplex
          (AddCommGrpCat.of ℤ)).d 1 0 := by
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro x
  rw [iota_affineSingularSubdivisionDiscrepancyChainMap, ← Category.assoc,
    iota_affineSingularSubdivisionPrismComponent]
  simp

/-- The transported prism gives the chain-homotopy identity in every positive degree. -/
public theorem affineSingularSubdivisionPrismComponent_identity_succ
    (X : TopCat.{0}) (n : ℕ) :
    (affineSingularSubdivisionChainMap X).f (n + 1) =
      ((TopCat.toSSet.obj X).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
          affineSingularSubdivisionPrismComponent X n +
        affineSingularSubdivisionPrismComponent X (n + 1) ≫
          ((TopCat.toSSet.obj X).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) +
        𝟙 (((TopCat.toSSet.obj X).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 1)) := by
  have h := affineSingularSubdivisionPrismComponent_discrepancy_succ X n
  change (affineSingularSubdivisionChainMap X).f (n + 1) - 𝟙 _ = _ at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

/-- The transported prism gives the chain-homotopy identity in degree zero. -/
public theorem affineSingularSubdivisionPrismComponent_identity_zero
    (X : TopCat.{0}) :
    (affineSingularSubdivisionChainMap X).f 0 =
      affineSingularSubdivisionPrismComponent X 0 ≫
          ((TopCat.toSSet.obj X).chainComplex
            (AddCommGrpCat.of ℤ)).d 1 0 +
        𝟙 (((TopCat.toSSet.obj X).chainComplex
          (AddCommGrpCat.of ℤ)).X 0) := by
  have h := affineSingularSubdivisionPrismComponent_discrepancy_zero X
  change (affineSingularSubdivisionChainMap X).f 0 - 𝟙 _ = _ at h
  rwa [sub_eq_iff_eq_add] at h

/-- The homotopy family, supported from degree `i` to degree `i+1`. -/
public noncomputable def affineSingularSubdivisionPrismHom
    (X : TopCat.{0}) (i j : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)).X i ⟶
      ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)).X j :=
  if h : j = i + 1 then by
    subst j
    exact affineSingularSubdivisionPrismComponent X i
  else 0

@[simp]
public theorem affineSingularSubdivisionPrismHom_succ
    (X : TopCat.{0}) (i : ℕ) :
    affineSingularSubdivisionPrismHom X i (i + 1) =
      affineSingularSubdivisionPrismComponent X i := by
  simp [affineSingularSubdivisionPrismHom]

/-- Affine barycentric subdivision is chain homotopic to the identity on the integral singular
chain complex of every topological space. -/
public noncomputable def affineSingularSubdivisionHomotopy
    (X : TopCat.{0}) :
    Homotopy (affineSingularSubdivisionChainMap X)
      (𝟙 ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ))) where
  hom := affineSingularSubdivisionPrismHom X
  zero i j hij := by
    rw [affineSingularSubdivisionPrismHom]
    split_ifs with h
    · exfalso
      apply hij
      rw [ComplexShape.down_Rel]
      exact h.symm
    · rfl
  comm i := by
    cases i with
    | zero =>
        rw [Homotopy.dNext_zero_chainComplex,
          Homotopy.prevD_chainComplex]
        simp only [affineSingularSubdivisionPrismHom_succ, zero_add,
          HomologicalComplex.id_f]
        exact affineSingularSubdivisionPrismComponent_identity_zero X
    | succ n =>
        rw [Homotopy.dNext_succ_chainComplex,
          Homotopy.prevD_chainComplex]
        simp only [affineSingularSubdivisionPrismHom_succ,
          HomologicalComplex.id_f]
        exact affineSingularSubdivisionPrismComponent_identity_succ X n


end AlgebraicTopology.Singular
