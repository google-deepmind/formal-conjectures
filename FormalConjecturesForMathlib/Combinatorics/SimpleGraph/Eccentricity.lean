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

public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Data.Real.Basic

@[expose] public section

namespace SimpleGraph
open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The set of vertices of maximum eccentricity. -/
noncomputable def maxEccentricityVertices (G : SimpleGraph α) : Set α :=
  {v : α | G.eccent v = G.ediam}

/-- The set of **boundary vertices** of `G`: vertices whose eccentricity equals the
maximum eccentricity (the diameter of `G`). This is the `Finset` counterpart of
`maxEccentricityVertices`. -/
noncomputable def boundaryVertices (G : SimpleGraph α) : Finset α :=
  Finset.univ.filter (fun v => G.eccent v = G.ediam)

/-- The average eccentricity of a graph `G`: the mean of `G.eccent v` over all vertices,
converted to a real number. Returns 0 if the graph has no vertices. -/
noncomputable def averageEccentricity (G : SimpleGraph α) : ℝ :=
  (∑ v : α, (G.eccent v).toNat) / (Fintype.card α : ℝ)

/-- The size of the periphery (number of vertices of maximum eccentricity). -/
noncomputable def peripherySize (G : SimpleGraph α) : ℕ :=
  G.boundaryVertices.card

end SimpleGraph
