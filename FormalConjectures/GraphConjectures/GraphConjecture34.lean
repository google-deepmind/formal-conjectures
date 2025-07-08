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

import FormalConjectures.GraphConjectures.Imports
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Invariants

open Finset
open scoped Classical

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/--
WOWII Conjecture 34 (open):
Let `path(G)` be the floor of the average distance of a connected graph `G`.
Then
`path(G) ≥ ceil( distavg(G, center) + distavg(G, maxEccentricityVertices G) )`.
-/
theorem conjecture34 [Nonempty α] (G : SimpleGraph α) (h_conn : G.Connected) :
  Int.ceil (distavg G (graphCenter G) + distavg G (maxEccentricityVertices G)) ≤ (path G : ℤ) := by
  sorry

end SimpleGraph
