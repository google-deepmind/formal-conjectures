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
# Erdős Problem 583

*References:*
- [erdosproblems.com/583](https://www.erdosproblems.com/583)
- [AnBa23] Anto, Nevil and Basavaraju, Manu, *Gallai's path decomposition for 2-degenerate graphs*.
  Discrete Math. Theor. Comput. Sci. (2023), Paper No. 16, 11.
- [BBB21] A. Blanché, M. Bonamy, and N. Bonichon, *Gallai's path decomposition in planar graphs*.
  arXiv:2110.08870 (2021).
- [BoPe19] Bonamy, Marthe and Perrett, Thomas J., *Gallai's path decomposition conjecture for graphs
  of small maximum degree*. Discrete Math. (2019), 1293--1299.
- [CFZ26] Chu, Yanan and Fan, Genghua and Zhou, Chuixiang, *Gallai's conjecture and the path number
  of odd semi-cliques*. Discrete Math. (2026), Paper No. 114725, 6.
- [Ch78] Chung, F. R. K., *On partitions of graphs into trees*. Discrete Math. (1978), 23-30.
- [DeKo00] Dean, Nathaniel and Kouider, Mekkia, *Gallai's conjecture for disconnected graphs*.
  Discrete Math. (2000), 43--54.
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Fa02] Fan, Genghua, *Subgraph coverings and edge switchings*. J. Combin. Theory Ser. B (2002),
  54-83.
- [Lo68] Lovász, L., *On covering of graphs*. Theory of Graphs (Proc. Colloq., Tihany, 1966) (1968),
  231-236.
- [Py96] Pyber, L., *Covering the edges of a connected graph by paths*. J. Combin. Theory Ser. B
  (1996), 152-159.
-/

open SimpleGraph

namespace Erdos583

/--
A subgraph `H` of `G` is a path subgraph if it is the subgraph traced out by a path in `G`,
i.e. a walk with no repeated vertices.
-/
def IsPathSubgraph {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) : Prop :=
  ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ H = p.toSubgraph

/--
Every connected graph on $n$ vertices can be partitioned into at most $\lceil n/2\rceil$
edge-disjoint paths.

A problem of Erdős and Gallai.
-/
@[category research open, AMS 5]
theorem erdos_583 {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsPathSubgraph H) ∧
      IsDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ) / 2⌉₊ := by
  sorry

end Erdos583
