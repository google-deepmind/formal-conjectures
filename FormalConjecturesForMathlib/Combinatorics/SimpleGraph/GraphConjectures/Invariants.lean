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
module

public import Mathlib
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Multiset.Interval

@[expose] public section

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Local eccentricity of a vertex. -/
noncomputable def local_eccentricity (G : SimpleGraph α) (v : α) : ENat :=
  sSup (Set.range (G.edist v))

/-- The set of vertices of maximum eccentricity. -/
noncomputable def maxEccentricityVertices (G : SimpleGraph α) : Set α :=
  {v : α | G.eccent v = G.ediam}

/-- The average eccentricity of a graph `G`: the mean of `G.eccent v` over all vertices,
converted to a real number. Returns 0 if the graph has no vertices. -/
noncomputable def averageEccentricity (G : SimpleGraph α) : ℝ :=
  (∑ v : α, (G.eccent v).toNat) / (Fintype.card α : ℝ)



/-- A family of paths covering all vertices without overlaps. -/
def IsPathCover (G : SimpleGraph α) (P : Finset (Finset α)) : Prop :=
  (∀ s1 ∈ P, ∀ s2 ∈ P, s1 ≠ s2 → Disjoint s1 s2) ∧
  (Finset.univ ⊆ P.biUnion id) ∧
  (∀ s ∈ P, ∃ (u v : α) (p : G.Walk u v), p.IsPath ∧ s = p.support.toFinset)

/-- Minimum size of a path cover of `G`. -/
noncomputable def pathCoverNumber (G : SimpleGraph α) : ℕ :=
  sInf { k | ∃ P : Finset (Finset α), P.card = k ∧ IsPathCover G P }

/-- The same quantity as a real number. -/
noncomputable def p (G : SimpleGraph α) : ℝ := (pathCoverNumber G : ℝ)


end SimpleGraph
