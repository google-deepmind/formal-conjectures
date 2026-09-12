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

import FormalConjecturesUtil

/-!
# Erdős Problem 1017

*References:*
- [erdosproblems.com/1017](https://www.erdosproblems.com/1017)
- [EGP66] Erdős, Paul and Goodman, A. W. and Pósa, Lajos, *The representation of a graph by set
  intersections*. Canadian J. Math. (1966), 106-112.
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [GyKe17] Győri, Ervin and Keszegh, Balázs, *On the number of edge-disjoint triangles in {$K_4$}-free
  graphs*. Combinatorica (2017), 1113--1124.
- [Lo68] Lovász, L., *On covering of graphs*. Theory of Graphs (Proc. Colloq., Tihany, 1966) (1968),
  231-236.
-/

open SimpleGraph

namespace Erdos1017

/--
A subgraph that is a complete graph on its vertex set.
-/
def IsCompleteGraph {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) : Prop :=
  Set.Pairwise H.verts H.Adj

/--
The clique partition number $f(n,k)$: the least $m$ such that every graph on $n$ vertices and $k$
edges can be partitioned into at most $m$ edge-disjoint complete graphs.
-/
noncomputable def f (n k : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ G : SimpleGraph (Fin n),
    G.edgeSet.ncard = k →
    ∃ D : Finset G.Subgraph,
      D.card ≤ m ∧ (∀ H ∈ D, IsCompleteGraph H) ∧ G.IsDecomposition D}

/--
Let $f(n,k)$ be such that every graph on $n$ vertices and $k$ edges can be partitioned into at most $f(n,k)$ edge-disjoint complete graphs. Estimate $f(n,k)$ for $k>n^2/4$.
-/
@[category research open, AMS 5]
theorem erdos_1017 :
    let ans : ℕ → ℕ → ℕ := answer(sorry)
    ∀ n k : ℕ, (n : ℝ) ^ 2 / 4 < (k : ℝ) → f n k = ans n k := by
  sorry

end Erdos1017
