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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 74

*Reference:* [erdosproblems.com/74](https://www.erdosproblems.com/74)
-/

open Filter SimpleGraph

open scoped Topology Real

namespace Erdos74

open Erdos74

universe u
variable {V : Type u}

/--
For a given Graph $G$, define a number such that any subgraph of G
on $n$ vertices can be made bipartite after deleting at most this many edges.
This is Definition 3.1 in [EHS82].

[EHS82] Erdős, P. and Hajnal, A. and Szemerédi, E.,
  *On almost bipartite large chromatic graphs* Theory and practice of combinatorics (1982), 117-123.
-/
noncomputable def SimpleGraph.max_subgraph_bipartite_edge_deletion_num
    (G : SimpleGraph V) (n : ℕ) : ℕ :=
  sSup { (sInf { (E.ncard) | (E : Set (Sym2 V)) (_ : IsBipartite (A.deleteEdges E).coe)}) |
    (A : Subgraph G) (_ : (A.verts.ncard = n))}


/--
Deleting all edges will always be sufficient to make the graph bipartite.
-/
@[category undergraduate, AMS 5]
lemma max_subgraph_edge_dist_bipartite_le (G : SimpleGraph V) (n : ℕ) :
    G.max_subgraph_bipartite_edge_deletion_num n ≤ n.choose 2 := by
  sorry

/--
Let $f(n)\to \infty$ possibly very slowly.
Is there a graph of infinite chromatic number such that every finite subgraph on $n$
vertices can be made bipartite by deleting at most $f(n)$ edges?
-/
@[category research open, AMS 5]
theorem erdos_74 : (∀ f : ℕ → ℕ, Tendsto f atTop atTop →
    (∃ G : SimpleGraph V, G.chromaticNumber = ⊤ ∧
    ∀ n, G.max_subgraph_bipartite_edge_deletion_num n ≤ f n)) ↔ answer(sorry):= by
  sorry

/--
Is there a graph of infinite chromatic number such that every finite subgraph on $n$
vertices can be made bipartite by deleting at most $\sqrt{n}$ edges?
-/
@[category research open, AMS 5]
theorem erdos_74.variants.sqrt : (∃ G : SimpleGraph V, G.chromaticNumber = ⊤ ∧
    ∀ n, G.max_subgraph_bipartite_edge_deletion_num n ≤ (n : ℝ).sqrt) ↔ answer(sorry):= by
  sorry

-- TODO(firsching): add the remaining statements/comments

end Erdos74
