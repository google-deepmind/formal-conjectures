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

import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.DiamExtra
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Domination
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.Bipartite
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Invariants
import FormalConjectures.Util.ProblemImports
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Int.Basic
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.ENat.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical

/--
WOWII [Conjecture 5](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`, `Ls(G)` is bounded below by the maximal size
of a sphere of radius `radius(G)` around the centres of `G`.
-/
@[category research solved, AMS 5]
theorem conjecture5 (G : SimpleGraph V) (h_conn : G.Connected) :
    letI centers := { v : V | G.eccent v = G.radius }
    letI r_nat := G.radius.toNat
    letI sphere_verts (v : V) : Set V := { w | G.dist v w = r_nat }
    letI sphere_size (v : V) : ℝ := ↑(Finset.univ.filter (fun w => w ∈ sphere_verts v)).card
    letI max_sphere_size := sSup (sphere_size '' centers)
    max_sphere_size ≤ Ls G := by
  sorry

end SimpleGraph
