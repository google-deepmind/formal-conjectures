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

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)

/--
WOWII Conjecture 58 (open):
For a connected graph `G`, the size `f(G)` of a largest induced forest satisfies
`f(G) ≥ ceil( b(G) / average l(v) )` where `b(G)` is the largest induced
bipartite subgraph and `l(v)` is the independence number of `G.neighborSet v`.
-/
-- The number of vertices of a largest induced forest of the graph.
-- WOWII conjecture: If G is a simple connected graph, then f(G) ≥ CEIL[ b(G)/average of l (v)]
theorem conjecture58 (hG : G.Connected) :
  (G.f : ℝ) ≥ Nat.ceil ((G.b : ℝ) / G.l_avg) := by sorry

end SimpleGraph
