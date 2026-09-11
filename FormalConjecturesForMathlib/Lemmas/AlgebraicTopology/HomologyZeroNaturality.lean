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

public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-!
# Naturality of the degree-zero homology augmentation

The augmentation is natural for actual simplicial and continuous maps. Consequently a
continuous map between path-connected spaces induces an isomorphism on degree-zero homology;
for a nonempty source and path-connected target the induced map is an epimorphism.

The augmentation proof generalizes the additive-group-valued proof in
`StandardSimplexSingularComparison` to arbitrary coefficient objects.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory Limits AlgebraicTopology HomologicalComplex
open scoped Simplicial

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C]

namespace SSet

/-- In a nonnegative chain complex the degree-zero chains are the degree-zero cycles. -/
def chainComplexXZeroIsoCyclesZero (K : ChainComplex C ℕ) : K.X 0 ≅ K.cycles 0 where
  hom := K.liftCycles (𝟙 _) 0 (by simp) (by simp)
  inv := K.iCycles 0
  hom_inv_id := by simp
  inv_hom_id := by
    rw [← cancel_mono (K.iCycles 0)]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the augmentation for any coefficient object. -/
@[reassoc]
theorem homology₀ε_naturality {X Y : SSet.{w}} (f : X ⟶ Y) (R : C) :
    SSet.homologyMap f R 0 ≫ Y.homology₀ε R = X.homology₀ε R := by
  let K := X.chainComplex R
  let L := Y.chainComplex R
  let φ := SSet.chainComplexMap f R
  let e₀ := chainComplexXZeroIsoCyclesZero K
  apply (cancel_epi (K.homologyπ 0)).1
  apply (cancel_epi e₀.hom).1
  apply X.chainComplex_hom_ext
  intro x
  change X.ιChainComplex x ≫ e₀.hom ≫ K.homologyπ 0 ≫
      HomologicalComplex.homologyMap φ 0 ≫ Y.homology₀ε R =
    X.ιChainComplex x ≫ e₀.hom ≫ K.homologyπ 0 ≫ X.homology₀ε R
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  change X.ιChainComplex x ≫ K.liftCycles (𝟙 _) 0 (by simp) (by simp) ≫
      HomologicalComplex.cyclesMap φ 0 ≫ L.homologyπ 0 ≫ Y.homology₀ε R =
    X.ιChainComplex x ≫ K.liftCycles (𝟙 _) 0 (by simp) (by simp) ≫
      K.homologyπ 0 ≫ X.homology₀ε R
  simp only [← Category.assoc, HomologicalComplex.comp_liftCycles, Category.comp_id,
    HomologicalComplex.liftCycles_comp_cyclesMap]
  simp only [Category.assoc]
  change L.liftCycles
      (X.ιChainComplex x ≫ (SSet.chainComplexMap f R).f 0) 0 (by simp) (by simp) ≫
        L.homologyπ 0 ≫ Y.homology₀ε R =
    K.liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
      K.homologyπ 0 ≫ X.homology₀ε R
  have hlift : L.liftCycles
      (X.ιChainComplex x ≫ (SSet.chainComplexMap f R).f 0) 0 (by simp) (by simp) =
      L.liftCycles (Y.ιChainComplex (f.app _ x)) 0 (by simp) (by simp) := by
    apply (cancel_mono (L.iCycles 0)).1
    simpa only [HomologicalComplex.liftCycles_i] using
      SSet.ι_chainComplexMap_f X Y f R x
  rw [hlift]
  exact (Y.liftCycles_ιChainComplex_homologyπ_homology₀ε R (f.app _ x)).trans
    (X.liftCycles_ιChainComplex_homologyπ_homology₀ε R x).symm

/-- A vertex provides a section of the degree-zero augmentation. -/
theorem homology₀ε_epi_of_vertex (X : SSet.{w}) (R : C) (x : X _⦋0⦌) :
    Epi (X.homology₀ε R) := by
  apply epi_of_epi_fac (f :=
    (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
      (X.chainComplex R).homologyπ 0) (h := 𝟙 R)
  simpa only [Category.assoc] using
    X.liftCycles_ιChainComplex_homologyπ_homology₀ε R x

end SSet

namespace TopCat

/-- Naturality of the singular degree-zero augmentation. -/
@[reassoc]
theorem singularHomology₀ε_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) (R : C) :
    ((singularHomologyFunctor C 0).obj R).map f ≫ Y.singularHomology₀ε R =
      X.singularHomology₀ε R :=
  SSet.homology₀ε_naturality (toSSet.map f) R

/-- A nonempty space has a surjective degree-zero augmentation. -/
theorem singularHomology₀ε_epi (X : TopCat.{w}) [Nonempty X] (R : C) :
    Epi (X.singularHomology₀ε R) :=
  SSet.homology₀ε_epi_of_vertex (toSSet.obj X) R
    ((X.toSSetObjEquiv _).symm (ContinuousMap.const _ (Classical.arbitrary X)))

/-- Any map into a path-connected space is surjective on degree-zero homology
provided its source is nonempty. -/
theorem singularHomologyMap_zero_epi {X Y : TopCat.{w}} [Nonempty X]
    [PathConnectedSpace Y] (f : X ⟶ Y) (R : C) :
    Epi (((singularHomologyFunctor C 0).obj R).map f) := by
  let : Epi (X.singularHomology₀ε R) := X.singularHomology₀ε_epi R
  have : Epi (((singularHomologyFunctor C 0).obj R).map f ≫
      Y.singularHomology₀ε R) := by
    rw [singularHomology₀ε_naturality]
    infer_instance
  exact (epi_comp_iff_of_isIso _ (Y.singularHomology₀ε R)).mp this

/-- Maps between path-connected spaces induce actual isomorphisms in degree zero. -/
theorem singularHomologyMap_zero_isIso {X Y : TopCat.{w}}
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y) (R : C) :
    IsIso (((singularHomologyFunctor C 0).obj R).map f) := by
  have : IsIso (((singularHomologyFunctor C 0).obj R).map f ≫
      Y.singularHomology₀ε R) := by
    rw [singularHomology₀ε_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (Y.singularHomology₀ε R)

end TopCat
