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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularChainSheafStalk

/-!
# Homology sheaves of the relative singular-chain complex

This module upgrades the chain-stalk comparison to the stalk of the actual homology sheaf,
using exactness of the sheaf stalk functor. In particular, vanishing of the homology sheaf is
equivalent to vanishing of all local relative homology groups. This proves the sheaf-theoretic
reduction needed for a manifold orientation theorem, without assuming local homology vanishing
or constructing an orientation by choosing arbitrary generators.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopCat.{u})

/-- The homology sheaf in homological degree `n` of the actual relative singular-chain sheaf
complex. Under the cohomological convention this is the homology sheaf in degree `-n`. -/
def singularChainHomologySheaf (n : ℕ) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (singularChainSheafComplex R X).homology n

/-- The stalk of the homology sheaf is canonically local relative singular homology. -/
def singularChainHomologySheafStalkIso [T2Space X] (x : X) (n : ℕ) :
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
        (singularChainHomologySheaf R X n) ≅
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        (RelativeHomology R (TopPair.ofSubset ({x} : Set X)ᶜ) n) :=
  (((singularChainSheafComplex R X).sc n).mapHomologyIso
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).symm ≪≫
    singularChainSheafStalkHomologyIso R X x n

/-- Local homology vanishing is exactly the obstruction to vanishing of the homology sheaf.
The right side uses the underlying additive groups of the actual local relative homology. -/
theorem singularChainHomologySheaf_isZero_iff [T2Space X] (n : ℕ) :
    IsZero (singularChainHomologySheaf R X n) ↔
      ∀ x : X, IsZero ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        (RelativeHomology R (TopPair.ofSubset ({x} : Set X)ᶜ) n)) := by
  rw [TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
  exact forall_congr' fun x ↦ (singularChainHomologySheafStalkIso R X x n).isZero_iff

/-- The homology sheaf vanishes whenever the actual local relative homology groups vanish. -/
theorem singularChainHomologySheaf_isZero_of_localHomology_isZero [T2Space X] (n : ℕ)
    (hlocal : ∀ x : X, IsZero (RelativeHomology R (TopPair.ofSubset ({x} : Set X)ᶜ) n)) :
    IsZero (singularChainHomologySheaf R X n) := by
  rw [singularChainHomologySheaf_isZero_iff]
  exact fun x ↦ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map_isZero (hlocal x)

end AlgebraicTopology.Singular
