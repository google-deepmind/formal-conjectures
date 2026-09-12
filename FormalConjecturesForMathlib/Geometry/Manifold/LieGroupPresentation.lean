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

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Topological groups admitting a Lie group structure

A topological group `G` *admits a Lie group structure* if it is continuously isomorphic to a
finite-dimensional real-analytic Lie group. Lie groups are Hausdorff but not assumed to be second
countable: every discrete group is a `0`-dimensional Lie group.

## Main definitions

- `LieGroupPresentation G n`: a continuous group isomorphism from `G` to an `n`-dimensional
  real-analytic Lie group.
- `AdmitsLieGroupStructure G`: `G` has a `LieGroupPresentation` in some finite dimension.

## Main results

- `admitsLieGroupStructure_of_lieGroup`: a Hausdorff real-analytic Lie group admits a Lie group
  structure.
- `admitsLieGroupStructure_of_discreteTopology`: a discrete group admits a Lie group structure.
- `AdmitsLieGroupStructure.locallyCompactSpace`: a group admitting a Lie group structure is
  locally compact.
-/

@[expose] public section

open scoped Manifold ContDiff

universe u

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- A continuous group isomorphism from `G` to an `n`-dimensional real-analytic Lie group.
The Lie group is not assumed to be second countable. -/
structure LieGroupPresentation (G : Type u) [TopologicalSpace G] [Group G] (n : ℕ) where
  carrier : Type u
  [topologicalSpace : TopologicalSpace carrier]
  [group : Group carrier]
  [t2Space : T2Space carrier]
  [chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin n)) carrier]
  [isManifold : IsManifold (𝓡 n) ω carrier]
  [lieGroup : LieGroup (𝓡 n) ω carrier]
  equiv : G ≃ₜ* carrier

/-- A topological group admits a Lie group structure if it has a `LieGroupPresentation` in some
finite dimension. -/
def AdmitsLieGroupStructure (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∃ n, Nonempty (LieGroupPresentation G n)

/-- Every Hausdorff finite-dimensional real-analytic Lie group admits a Lie group structure. -/
theorem admitsLieGroupStructure_of_lieGroup {n : ℕ} [T2Space G]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) G] [LieGroup (𝓡 n) ω G] :
    AdmitsLieGroupStructure G :=
  ⟨n, ⟨{ carrier := G, equiv := ContinuousMulEquiv.refl G }⟩⟩

/-- Every discrete group is a `0`-dimensional Lie group. -/
theorem admitsLieGroupStructure_of_discreteTopology [DiscreteTopology G] :
    AdmitsLieGroupStructure G := by
  let := ChartedSpace.ofDiscreteTopology (M := G) (H := EuclideanSpace ℝ (Fin 0))
  have := IsManifold.of_discreteTopology (𝕜 := ℝ) (M := G) (E := EuclideanSpace ℝ (Fin 0)) ω
  have : LieGroup (𝓡 0) ω G :=
    { contMDiff_mul := contMDiff_of_discreteTopology
      contMDiff_inv := contMDiff_of_discreteTopology }
  exact admitsLieGroupStructure_of_lieGroup (n := 0)

/-- A group admitting a Lie group structure is locally compact. -/
theorem AdmitsLieGroupStructure.locallyCompactSpace (h : AdmitsLieGroupStructure G) :
    LocallyCompactSpace G := by
  obtain ⟨k, ⟨p⟩⟩ := h
  let := p.topologicalSpace
  let := p.group
  let := p.chartedSpace
  have := (𝓡 k).locallyCompactSpace
  have : LocallyCompactSpace p.carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin k)) p.carrier
  exact p.equiv.toHomeomorph.locallyCompactSpace_iff.mpr inferInstance
