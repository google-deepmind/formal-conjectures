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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularAffineSubdivisionPrism
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularAffineSubdivisionSmall

import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
This module is ported from Paul Lezeau's corresponding file in
`sphere-six-complex` pull request #49, under the Apache-2.0 license.

# The affine subdivision prism on cover-small singular chains

The universal affine prism only precomposes a singular simplex.  It therefore preserves the
range of any cover member, just as affine subdivision itself does.  This file restricts the
prism to the cover-small chain complex and proves that cover-small affine subdivision is chain
homotopic to the identity there.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set

namespace AlgebraicTopology.Singular

variable {iota : Type} (X : TopCat) (U : iota → Set X)

/-- The affine prism on a selected lift of a cover-small generator, mapped back into the small
chain complex. -/
public noncomputable def coverSmallAffinePrismSimplexChain
    (n : ℕ)
    (x : (coverSmallSingularSubcomplex X U : SSet).obj
      (Opposite.op (SimplexCategory.mk n))) :
    AddCommGrpCat.of ℤ ⟶
      (CoverSmallIntegralSingularChainComplex X U).X (n + 1) :=
  (TopCat.toSSet.obj
      (TopCat.of (U (coverSmallSimplexPreimageIndex X U x)))).ιChainComplex
        (coverSmallSimplexPreimage X U x) ≫
    affineSingularSubdivisionPrismComponent
      (TopCat.of (U (coverSmallSimplexPreimageIndex X U x))) n ≫
    (coverMemberToSmallIntegralSingularChains X U
      (coverSmallSimplexPreimageIndex X U x)).f (n + 1)

/-- The degree-raising affine prism operator on cover-small chains. -/
public noncomputable def coverSmallAffinePrismComponent (n : ℕ) :
    (CoverSmallIntegralSingularChainComplex X U).X n ⟶
      (CoverSmallIntegralSingularChainComplex X U).X (n + 1) :=
  Sigma.desc (coverSmallAffinePrismSimplexChain X U n)

@[reassoc (attr := simp)]
public theorem iota_coverSmallAffinePrismComponent
    (n : ℕ)
    (x : (coverSmallSingularSubcomplex X U : SSet).obj
      (Opposite.op (SimplexCategory.mk n))) :
    (coverSmallSingularSubcomplex X U : SSet).ιChainComplex x ≫
        coverSmallAffinePrismComponent X U n =
      coverSmallAffinePrismSimplexChain X U n x := by
  apply Sigma.ι_desc

/-- The small prism on a generator agrees with the full prism after inclusion. -/
public theorem coverSmallAffinePrismSimplexChain_comp_inclusion
    (n : ℕ)
    (x : (coverSmallSingularSubcomplex X U : SSet).obj
      (Opposite.op (SimplexCategory.mk n))) :
    coverSmallAffinePrismSimplexChain X U n x ≫
        (coverSmallIntegralSingularChainInclusion X U).f (n + 1) =
      (TopCat.toSSet.obj X).ιChainComplex x.1 ≫
        affineSingularSubdivisionPrismComponent X n := by
  let j := coverSmallSimplexPreimageIndex X U x
  let y := coverSmallSimplexPreimage X U x
  let I := SSet.chainComplexMap
    (TopCat.toSSet.map (topologicalSubsetInclusion X (U j)))
    (AddCommGrpCat.of ℤ)
  have hcover := congrArg (fun F ↦ F.f (n + 1))
    (coverMemberToSmallIntegralSingularChains_comp_inclusion X U j)
  change (SSet.chainComplexMap (coverMemberToSmallSingularSet X U j)
        (AddCommGrpCat.of ℤ)).f (n + 1) ≫
      (SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)).f (n + 1) = I.f (n + 1) at hcover
  change (((TopCat.toSSet.obj (TopCat.of (U j))).ιChainComplex y ≫
      affineSingularSubdivisionPrismComponent (TopCat.of (U j)) n) ≫
        (SSet.chainComplexMap (coverMemberToSmallSingularSet X U j)
          (AddCommGrpCat.of ℤ)).f (n + 1)) ≫
      (SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)).f (n + 1) = _
  rw [Category.assoc, hcover, Category.assoc,
    ← affineSingularSubdivisionPrismComponent_naturality, ← Category.assoc,
    SSet.ι_chainComplexMap_f, show (TopCat.toSSet.map
      (topologicalSubsetInclusion X (U j))).app _ y = x.1 from
    coverSmallSimplexPreimage_spec X U x]

/-- The small prism agrees degreewise with the full prism after inclusion. -/
public theorem coverSmallAffinePrismComponent_comp_inclusion
    (n : ℕ) :
    coverSmallAffinePrismComponent X U n ≫
        (coverSmallIntegralSingularChainInclusion X U).f (n + 1) =
      (coverSmallIntegralSingularChainInclusion X U).f n ≫
        affineSingularSubdivisionPrismComponent X n := by
  change coverSmallAffinePrismComponent X U n ≫
      (SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)).f (n + 1) =
    (SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
      (AddCommGrpCat.of ℤ)).f n ≫
      affineSingularSubdivisionPrismComponent X n
  apply (coverSmallSingularSubcomplex X U : SSet).chainComplex_hom_ext
  intro x
  rw [← Category.assoc, iota_coverSmallAffinePrismComponent]
  simp only [SSet.ι_chainComplexMap_f_assoc]
  exact coverSmallAffinePrismSimplexChain_comp_inclusion X U n x

set_option linter.style.haveILetI false in
/-- The cover-small prism gives the chain-homotopy equation in positive degrees. -/
public theorem coverSmallAffinePrismComponent_identity_succ
    (n : ℕ) :
    (coverSmallAffineSubdivisionChainMap X U).f (n + 1) =
      (CoverSmallIntegralSingularChainComplex X U).d (n + 1) n ≫
          coverSmallAffinePrismComponent X U n +
        coverSmallAffinePrismComponent X U (n + 1) ≫
          (CoverSmallIntegralSingularChainComplex X U).d (n + 2) (n + 1) +
        𝟙 ((CoverSmallIntegralSingularChainComplex X U).X (n + 1)) := by
  let I := SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
    (AddCommGrpCat.of ℤ)
  haveI : Mono I := by
    dsimp [I]
    exact coverSmallIntegralSingularChainInclusion_mono X U
  haveI : Mono (I.f (n + 1)) := by
    change Mono ((HomologicalComplex.eval AddCommGrpCat
      (ComplexShape.down ℕ) (n + 1)).map I)
    infer_instance
  apply (cancel_mono (I.f (n + 1))).mp
  rw [Preadditive.add_comp, Preadditive.add_comp]
  simp only [Category.id_comp]
  rw [coverSmallAffineSubdivisionChainMap_f]
  have hA := coverSmallAffineSubdivisionComponent_comp_inclusion X U (n + 1)
  change coverSmallAffineSubdivisionComponent X U (n + 1) ≫ I.f (n + 1) =
    I.f (n + 1) ≫ affineSingularSubdivisionComponent X (n + 1) at hA
  have hP (k : ℕ) :
      coverSmallAffinePrismComponent X U k ≫ I.f (k + 1) =
        I.f k ≫ affineSingularSubdivisionPrismComponent X k :=
    coverSmallAffinePrismComponent_comp_inclusion X U k
  rw [hA]
  change I.f (n + 1) ≫
      (affineSingularSubdivisionChainMap X).f (n + 1) = _
  rw [affineSingularSubdivisionPrismComponent_identity_succ,
    Preadditive.comp_add, Preadditive.comp_add]
  simp only [Category.comp_id]
  apply congrArg₂ (fun a b ↦ a + b)
  · apply congrArg₂ (fun a b ↦ a + b)
    · rw [← Category.assoc, I.comm, Category.assoc, ← hP, ← Category.assoc]
    · rw [← Category.assoc, ← hP, Category.assoc, I.comm, ← Category.assoc]
  · rfl

set_option linter.style.haveILetI false in
/-- The cover-small prism gives the chain-homotopy equation in degree zero. -/
public theorem coverSmallAffinePrismComponent_identity_zero :
    (coverSmallAffineSubdivisionChainMap X U).f 0 =
      coverSmallAffinePrismComponent X U 0 ≫
          (CoverSmallIntegralSingularChainComplex X U).d 1 0 +
        𝟙 ((CoverSmallIntegralSingularChainComplex X U).X 0) := by
  let I := SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
    (AddCommGrpCat.of ℤ)
  haveI : Mono I := by
    dsimp [I]
    exact coverSmallIntegralSingularChainInclusion_mono X U
  haveI : Mono (I.f 0) := by
    change Mono ((HomologicalComplex.eval AddCommGrpCat
      (ComplexShape.down ℕ) 0).map I)
    infer_instance
  apply (cancel_mono (I.f 0)).mp
  rw [Preadditive.add_comp]
  simp only [Category.id_comp]
  rw [coverSmallAffineSubdivisionChainMap_f]
  have hA := coverSmallAffineSubdivisionComponent_comp_inclusion X U 0
  change coverSmallAffineSubdivisionComponent X U 0 ≫ I.f 0 =
    I.f 0 ≫ affineSingularSubdivisionComponent X 0 at hA
  have hP : coverSmallAffinePrismComponent X U 0 ≫ I.f 1 =
      I.f 0 ≫ affineSingularSubdivisionPrismComponent X 0 :=
    coverSmallAffinePrismComponent_comp_inclusion X U 0
  rw [hA]
  change I.f 0 ≫ (affineSingularSubdivisionChainMap X).f 0 = _
  rw [affineSingularSubdivisionPrismComponent_identity_zero,
    Preadditive.comp_add]
  simp only [Category.comp_id]
  apply congrArg₂ (fun a b ↦ a + b)
  · rw [← Category.assoc, ← hP, Category.assoc, I.comm, ← Category.assoc]
  · rfl

/-- The degree-raising small-prism family. -/
public noncomputable def coverSmallAffinePrismHom (i j : ℕ) :
    (CoverSmallIntegralSingularChainComplex X U).X i ⟶
      (CoverSmallIntegralSingularChainComplex X U).X j :=
  if h : j = i + 1 then by
    subst j
    exact coverSmallAffinePrismComponent X U i
  else 0

@[simp]
public theorem coverSmallAffinePrismHom_succ (i : ℕ) :
    coverSmallAffinePrismHom X U i (i + 1) =
      coverSmallAffinePrismComponent X U i := by
  simp [coverSmallAffinePrismHom]

/-- Cover-small affine subdivision is chain homotopic to the identity. -/
public noncomputable def coverSmallAffineSubdivisionHomotopy :
    Homotopy (coverSmallAffineSubdivisionChainMap X U)
      (𝟙 (CoverSmallIntegralSingularChainComplex X U)) where
  hom := coverSmallAffinePrismHom X U
  zero i j hij := by
    rw [coverSmallAffinePrismHom]
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
        simp only [coverSmallAffinePrismHom_succ, zero_add,
          HomologicalComplex.id_f]
        exact coverSmallAffinePrismComponent_identity_zero X U
    | succ n =>
        rw [Homotopy.dNext_succ_chainComplex,
          Homotopy.prevD_chainComplex]
        simp only [coverSmallAffinePrismHom_succ,
          HomologicalComplex.id_f]
        exact coverSmallAffinePrismComponent_identity_succ X U n

end AlgebraicTopology.Singular
