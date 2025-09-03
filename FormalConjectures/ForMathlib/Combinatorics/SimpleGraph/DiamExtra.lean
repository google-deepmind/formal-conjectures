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

-- Authors: Rida Hamadani

import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!

# Diameter of a simple graph

This module defines the eccentricity of vertices, the diameter, and the radius of a simple graph.

## Main definitions

    * `SimpleGraph.eccent`: the eccentricity of a vertex in a simple graph, which is the maximum
      distances between it and the other vertices.
    * `SimpleGraph.ediam`: the graph extended diameter, which is the maximum eccentricity.
      It is `ℕ∞`-valued.
    * `SimpleGraph.diam`: the graph diameter, an `ℕ`-valued version of `SimpleGraph.ediam`.
    * `SimpleGraph.radius`: the graph radius, which is the minimum eccentricity. It is `ℕ∞`-valued.
    * `SimpleGraph.center`: the set of vertices with eccentricity equal to the graph's radius.

-/

assert_not_exists Field

namespace SimpleGraph
variable {α : Type*} {G G' : SimpleGraph α}

/--
The diameter is the greatest distance between any two vertices. If the graph is disconnected,
this will be `0`.
-/
lemma diam_eq_zero_of_subsingleton [Subsingleton α] : G.diam = 0 := by
  simp [diam, ediam_eq_zero_iff_subsingleton.mpr (by assumption)]

proof_wanted diam_ne_zero [Nontrivial α] : G.diam ≠ 0

lemma nontrivial_of_diam_ne_zero' (h : G.diam ≠ 0) : Nontrivial α := by
  contrapose! h
  rw [not_nontrivial_iff_subsingleton] at h
  exact diam_eq_zero_of_subsingleton


section Path
open Path

proof_wanted dist_le_diam_of_mem_path {G : SimpleGraph α} {u v : α} (p : G.Walk u v) (w : α)
    (hw : w ∈ p.support) : G.dist w u ≤ G.diam

end Path

end SimpleGraph
