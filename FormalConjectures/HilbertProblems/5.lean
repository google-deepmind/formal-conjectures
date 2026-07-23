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
- [Pardon, *The Hilbert–Smith conjecture for three-manifolds*, JAMS 26 (2013)]
  (https://www.ams.org/journals/jams/2013-26-03/S0894-0347-2013-00766-3/)
- [van den Dries–Goldbring, *Hilbert's Fifth Problem*]
  (https://ems.press/journals/lem/articles/13621)
- [arXiv:math/0103145](https://arxiv.org/abs/math/0103145)
-/

namespace Hilbert5

open scoped Manifold ContDiff EuclideanGeometry

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

/-- A topological group `G` admits a Lie group structure if there exists a finite-dimensional
real-analytic manifold structure on `G` making its group operations real analytic. -/
def AdmitsLieGroupStructure (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ (k : ℕ) (cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) G),
    letI := cs
    IsManifold (𝓡 k) ω G ∧ LieGroup (𝓡 k) ω G

/-- Every Lie group trivially admits a Lie group structure. -/
@[category API, AMS 22]
theorem admitsLieGroupStructure_of_lieGroup
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) G]
    [IsManifold (𝓡 n) ω G] [LieGroup (𝓡 n) ω G] :
    AdmitsLieGroupStructure G :=
  ⟨n, inferInstance, inferInstance, inferInstance⟩

/-- A group admitting a Lie group structure is locally compact. -/
@[category API, AMS 22]
theorem locallyCompact_of_admitsLieGroupStructure
    (h : AdmitsLieGroupStructure G) : LocallyCompactSpace G := by
  obtain ⟨k, cs, hG, _⟩ := h
  haveI := cs
  haveI := hG
  haveI := (𝓡 k).locallyCompactSpace
  exact ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin k)) G

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
See [Pardon, Theorem 1.5]
(https://www.ams.org/journals/jams/2013-26-03/S0894-0347-2013-00766-3/). -/
@[category research solved, AMS 22 57 58]
theorem hilbert_smith_conjecture.variants.dimension_three {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MulAction G X] [ContinuousSMul G X] [FaithfulSMul G X] :
    AdmitsLieGroupStructure G := by
  sorry

/-- Pardon (2013), Theorem 1.5: the $p$-adic integers cannot act continuously and faithfully
on a connected 3-manifold. -/
@[category research solved, AMS 20 22 54 57]
theorem hilbert_smith_padic_formulation.variants.dimension_three (p : ℕ) [Fact p.Prime]
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [AddAction (PadicInt p) X] [ContinuousVAdd (PadicInt p) X]
    [FaithfulVAdd (PadicInt p) X] :
    False := by
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
topological group admits a compatible real-analytic Lie group structure. -/
@[category research solved, AMS 22 57]
theorem hilbert_fifth_problem
    [IsTopologicalGroup G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) G] :
    AdmitsLieGroupStructure G := by
  sorry

end Hilbert5
