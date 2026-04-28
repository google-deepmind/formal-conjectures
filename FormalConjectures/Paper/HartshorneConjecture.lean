/-
Copyright 2025 The Formal Conjectures Authors.

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
import FormalConjectures.Util.ProblemImports

/-! # Hartshorne's conjecture on Vector Bundles

*Reference*: [Varieties of small codimension in projective space](https://projecteuclid.org/journals/bulletin-of-the-american-mathematical-society-new-series/volume-80/issue-6/Varieties-of-small-codimension-in-projective-space/bams/1183535999.full)
by *R. Hartshorne*
-/

namespace HartshorneConjecture

open HartshorneConjecture

universe u

open CategoryTheory Limits MvPolynomial AlgebraicGeometry

variable (S : Scheme.{u})

namespace AlgebraicGeometry.Scheme

attribute [local instance] CategoryTheory.Types.instConcreteCategory Types.instFunLike

-- TODO(lezeau): explain/investigate why the following two instances are needed.

local instance (X : TopologicalSpace.Opens S) :
    ((Opens.grothendieckTopology S).over X).WEqualsLocallyBijective (Type u) :=
  CategoryTheory.GrothendieckTopology.instWEqualsLocallyBijectiveTypeHomObjForget
    ((Opens.grothendieckTopology S).over X)

local instance (X : TopologicalSpace.Opens S) :
    ((Opens.grothendieckTopology S).over X).WEqualsLocallyBijective (AddCommGrpCat.{u}) :=
  inferInstance

/--
A vector bundle over a scheme `S` is a locally free $\mathcal{O}_S$-module of finite rank.
-/
structure VectorBundles where
  carrier : S.Modules
  rank : ℕ
  isLocallyFreeFiniteConstantRank : SheafOfModules.IsVectorBundleWithRank
    (J := Opens.grothendieckTopology S) carrier rank

instance (S : Scheme) : Coe S.VectorBundles S.Modules where
  coe 𝓕 := 𝓕.carrier

/--
Vector bundles form a category.
-/
instance : Category S.VectorBundles :=
  inferInstanceAs <| Category <| InducedCategory _ VectorBundles.carrier

def VectorBundles.toModule : S.VectorBundles ⥤ S.Modules where
  obj 𝓕 := 𝓕.carrier
  map f := f.hom

@[category API, AMS 14]
theorem hasFiniteCoproductsVectorBundles : HasFiniteCoproducts S.VectorBundles := by
  sorry

instance : HasFiniteCoproducts S.VectorBundles :=
  hasFiniteCoproductsVectorBundles S

variable {S} in
/--
A splitting of a vector bundle `𝓕` is a non-trivial direct sum decomposition of `𝓕`
-/
structure VectorBundles.Splitting (𝓕 : S.VectorBundles) (ι : Type) [Fintype ι] [Nonempty ι] where
  components : ι → S.VectorBundles
  iso : 𝓕 ≅ ∐ components
  non_trivial : ∀ i, IsEmpty (components i ≅ 𝓕)

instance {S : Scheme} (𝓕 : S.VectorBundles) (ι : Type) [Fintype ι] [Nonempty ι] :
    CoeOut (𝓕.Splitting ι) (ι → S.VectorBundles) where
  coe s := s.components

end AlgebraicGeometry.Scheme
-- TODO(lezeau): here we would really need some sanity checks and easier results.

open AlgebraicGeometry.Scheme

/--
There are no indecomposable vector bundles of rank 2 on $\mathbb{P}^n$ for $n \ge 7$.
This is conjecture 6.3 in _VARIETIES OF SMALL CODIMENSION IN PROJECTIVE SPACE_, R. Hartshorne
-/
@[category research open, AMS 14]
theorem harthshorne_conjecture (n : ℕ) (hn : 7 ≤ n)
    (𝓕 : VectorBundles ℙ(Fin (n + 1); Spec (.of ℂ)))
    (h𝓕 : 𝓕.rank = 2) :
    Nonempty (𝓕.Splitting (Fin 2)) := by
  sorry

end HartshorneConjecture
