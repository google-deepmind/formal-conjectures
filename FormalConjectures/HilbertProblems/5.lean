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

import FormalConjectures.Util.ProblemImports

/-!
# Hilbert's Fifth Problem and the Hilbert–Smith Conjecture

The **Hilbert–Smith conjecture** states that a locally compact topological group acting
continuously and faithfully on a connected finite-dimensional topological manifold must be a
Lie group. It remains open in general; Pardon proved it for 3-manifolds in 2013.
An equivalent formulation: no p-adic integer group `ℤ_[p]` can act faithfully on any
connected finite-dimensional topological manifold.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Hilbert%E2%80%93Smith_conjecture)
- [Tao's blog](https://terrytao.wordpress.com/2011/08/13/the-hilbert-smith-conjecture/)
- [Pardon 2013, arXiv:1112.2324](https://arxiv.org/abs/1112.2324)
- [van den Dries–Goldbring, *Hilbert's Fifth Problem*]
  (https://ems.press/journals/lem/articles/13621)
- [arXiv:math/0103145](https://arxiv.org/abs/math/0103145)
-/

namespace Hilbert5

open scoped Manifold ContDiff EuclideanGeometry

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

/-- A presentation of `G` as a finite-dimensional real-analytic Lie group of dimension `n`.

`IsManifold` requires analytic transition maps between charts, while `LieGroup` requires analytic
multiplication and inversion. Both are needed to express the usual mathematical meaning of a
real-analytic Lie group in Mathlib. -/
structure LieGroupPresentation (G : Type u) [TopologicalSpace G] [Group G] (n : ℕ) where
  carrier : Type u
  [topologicalSpace : TopologicalSpace carrier]
  [group : Group carrier]
  [t2Space : T2Space carrier]
  [secondCountableTopology : SecondCountableTopology carrier]
  [chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin n)) carrier]
  [isManifold : IsManifold (𝓡 n) ω carrier]
  [lieGroup : LieGroup (𝓡 n) ω carrier]
  equiv : G ≃ₜ* carrier

/-- A topological group admits a Lie group structure if it is continuously isomorphic to some
finite-dimensional real-analytic Lie group. -/
def AdmitsLieGroupStructure (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∃ n, Nonempty (LieGroupPresentation G n)

/-- Every Lie group trivially admits a Lie group structure. -/
@[category API, AMS 22]
theorem admitsLieGroupStructure_of_lieGroup
    [T2Space G] [SecondCountableTopology G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) G]
    [IsManifold (𝓡 n) ω G] [LieGroup (𝓡 n) ω G] :
    AdmitsLieGroupStructure G :=
  ⟨n, ⟨{ carrier := G, equiv := ContinuousMulEquiv.refl G }⟩⟩

/-- A group admitting a Lie group structure is locally compact. -/
@[category API, AMS 22]
theorem locallyCompact_of_admitsLieGroupStructure
    (h : AdmitsLieGroupStructure G) : LocallyCompactSpace G := by
  obtain ⟨k, ⟨p⟩⟩ := h
  letI := p.topologicalSpace
  letI := p.group
  letI := p.chartedSpace
  haveI := (𝓡 k).locallyCompactSpace
  haveI : LocallyCompactSpace p.carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin k)) p.carrier
  exact p.equiv.toHomeomorph.isClosedEmbedding.locallyCompactSpace

/-- **Hilbert–Smith conjecture**: every locally compact topological group acting continuously
and faithfully on a connected finite-dimensional topological manifold is a Lie group. -/
@[category research open, AMS 22 57 58]
theorem hilbert_smith_conjecture
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MulAction G X] [ContinuousSMul G X] [FaithfulSMul G X] :
    AdmitsLieGroupStructure G := by
  sorry

/-- The conjecture holds when `G` acts by isometries on a Riemannian manifold, since `G`
embeds as a closed subgroup of the isometry group, which is a Lie group by Myers–Steenrod. -/
@[category research solved, AMS 22 53 57 58]
theorem hilbert_smith_conjecture.variants.riemannian
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MulAction G X] [ContinuousSMul G X] [FaithfulSMul G X]
    [MetricSpace X] [IsManifold (𝓡 n) ∞ X]
    (hiso : ∀ g : G, Isometry (g • · : X → X)) :
    AdmitsLieGroupStructure G := by
  sorry

/-- Pardon (2013): the Hilbert–Smith conjecture holds for 3-dimensional manifolds.
See [arXiv:1112.2324](https://arxiv.org/abs/1112.2324). -/
@[category research solved, AMS 22 57 58]
theorem hilbert_smith_conjecture.variants.dimension_three {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MulAction G X] [ContinuousSMul G X] [FaithfulSMul G X] :
    AdmitsLieGroupStructure G := by
  sorry

/-- Equivalent p-adic formulation: the p-adic integers `ℤ_[p]` cannot act continuously and
faithfully on any connected finite-dimensional topological manifold. By the Gleason–Yamabe
theorem, this is equivalent to `hilbert_smith_conjecture`. -/
@[category research open, AMS 22 57 58]
theorem hilbert_smith_padic_formulation (p : ℕ) [Fact p.Prime]
    [AddAction (PadicInt p) X] [ContinuousVAdd (PadicInt p) X]
    [FaithfulVAdd (PadicInt p) X] :
    False := by
  sorry

/-- **Hilbert's fifth problem** (Gleason–Montgomery–Zippin, 1952): every locally Euclidean
topological group is a Lie group. -/
@[category research solved, AMS 22 57]
theorem hilbert_fifth_problem
    [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) G] :
    Nonempty (LieGroupPresentation G n) := by
  sorry

end Hilbert5
