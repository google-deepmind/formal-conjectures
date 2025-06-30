/-
Copyright (c) 2025 Henryk Michalewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henryk Michalewski
-/

import FormalConjectures.GraphConjectures.Imports
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Invariants

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical

/--
WOWII Conjecture 5 (resolved):
For a simple connected graph `G`, `Ls(G)` is bounded below by the maximal size
of a sphere of radius `radius(G)` around the centres of `G`.
-/
theorem conjecture5 (G : SimpleGraph V) (h_conn : G.Connected) :
  let centers := { v : V | G.eccent v = G.radius }
  let r_nat := G.radius.toNat
  let sphere_verts (v : V) : Set V := { w | G.dist v w = r_nat }
  let sphere_size (v : V) : ℝ := ↑(Finset.univ.filter (fun w => w ∈ sphere_verts v)).card
  let max_sphere_size := sSup (sphere_size '' centers)
  Ls G ≥ max_sphere_size := by sorry

end SimpleGraph
