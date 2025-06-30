/-
Copyright (c) 2025 Henryk Michalewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henryk Michalewski
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
  (path G : ℤ) ≥ Int.ceil (distavg G (graphCenter G) + distavg G (maxEccentricityVertices G)) := by
  sorry

end SimpleGraph
