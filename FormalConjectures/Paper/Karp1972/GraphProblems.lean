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
# Karp's NP-complete graph problems

*References:*
* [Ka72] Karp, R. M., *Reducibility among Combinatorial Problems*.
  In *Complexity of Computer Computations*, Plenum (1972), pp. 85–103.
  §4, Theorem 3 and Main Theorem items 3, 5, 9, 10, 12, pp. 93–95.
  https://doi.org/10.1007/978-1-4684-2001-2_9.
-/

namespace Karp1972

open ComplexityTheory Computability.MatrixGraph

/-- **CLIQUE** ([Ka72], item 3, p. 94). No deterministic polynomial-time algorithm decides
whether a finite simple graph, given by a square symmetric loopless Boolean adjacency matrix,
contains $k$ mutually adjacent vertices, where the positive integer $k$ is given in binary.
CLIQUE is NP-complete, so this conjecture is equivalent to $P \ne NP$ (`P_ne_NP`). -/
@[category research open, AMS 5 68]
theorem clique_not_polytime : ¬ HasPolyTimeDecider Clique := by
  sorry

/-- **NODE COVER** ([Ka72], item 5, p. 94). No deterministic polynomial-time algorithm decides
whether a finite simple graph, given by its Boolean adjacency matrix, has a vertex set of size
at most $k$ meeting every edge, where the positive bound $k$ is given in binary.
Vertex cover is NP-complete, so this conjecture is equivalent to $P \ne NP$ (`P_ne_NP`). -/
@[category research open, AMS 5 68]
theorem vertexCover_not_polytime : ¬ HasPolyTimeDecider VertexCover := by
  sorry

/-- **CHROMATIC NUMBER** ([Ka72], item 12, p. 95). No deterministic polynomial-time algorithm
decides whether a finite simple graph, given by its Boolean adjacency matrix, has a proper
vertex coloring with at most $k$ colors. The positive binary bound $k$ is part of the input.
This problem is NP-complete, so the conjecture is equivalent to $P \ne NP$ (`P_ne_NP`). -/
@[category research open, AMS 5 68]
theorem colorable_not_polytime : ¬ HasPolyTimeDecider Colorable := by
  sorry

/-- **DIRECTED HAMILTON CIRCUIT** ([Ka72], item 9, p. 94). No deterministic polynomial-time
algorithm decides whether a finite loopless digraph, given by its Boolean adjacency matrix,
has a directed cycle visiting every vertex exactly once. Cycles have at least two vertices.
This problem is NP-complete, so the conjecture is equivalent to $P \ne NP$ (`P_ne_NP`). -/
@[category research open, AMS 5 68]
theorem directedHamiltonian_not_polytime : ¬ HasPolyTimeDecider DirectedHamiltonian := by
  sorry

/-- **UNDIRECTED HAMILTON CIRCUIT** ([Ka72], item 10, p. 94). No deterministic polynomial-time
algorithm decides whether a finite simple graph, given by its Boolean adjacency matrix, has
a cycle visiting every vertex exactly once. Cycles have at least three vertices.
This problem is NP-complete, so the conjecture is equivalent to $P \ne NP$ (`P_ne_NP`). -/
@[category research open, AMS 5 68]
theorem undirectedHamiltonian_not_polytime : ¬ HasPolyTimeDecider UndirectedHamiltonian := by
  sorry

end Karp1972
