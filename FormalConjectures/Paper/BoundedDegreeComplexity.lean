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
# Bounded-degree coloring, vertex cover, Hamiltonicity and matching

*References:*
- Garey, Johnson, and Stockmeyer, *Some simplified NP-complete graph problems*,
  Theoretical Computer Science 1 (1976), pp. 237–267,
  https://doi.org/10.1016/0304-3975(76)90059-1,
  Theorem 2.3 (pp. 251–252), Theorem 2.6 (pp. 260–262), and appendix (p. 267).
- Holyer, *The NP-Completeness of Edge-Coloring*, SIAM Journal on Computing 10 (1981),
  pp. 718–720, https://doi.org/10.1137/0210055, §4.
- Garey, Johnson, and Tarjan, *The Planar Hamiltonian Circuit Problem is NP-Complete*,
  SIAM Journal on Computing 5 (1976), pp. 704–714, https://doi.org/10.1137/0205049,
  pp. 704–705.
- Schaefer, *The Complexity of Satisfiability Problems*, STOC (1978), pp. 216–226,
  https://doi.org/10.1145/800133.804350, p. 217 and Theorem 7.1 / its comment on p. 225.
- Demaine, Karntikoon, and Pitimanaaree, *2-Colorable Perfect Matching is NP-complete in
  2-Connected 3-Regular Planar Graphs*, Theory of Computing Systems 69, article 22 (2025),
  https://doi.org/10.1007/s00224-025-10221-2, Theorem 3.
-/

namespace BoundedDegreeComplexity

open ComplexityTheory Computability.MatrixGraph

/-- **DEGREE-FOUR 3-COLORABILITY** (Garey–Johnson–Stockmeyer, Theorem 2.3).
Input: a square, symmetric, loopless Boolean adjacency matrix of maximum degree at most four.
Property: the vertices admit a proper coloring with three colors. No planarity restriction is
imposed; the empty graph accepts. This problem is NP-complete, so the nonexistence of a
deterministic polynomial-time decider for its binary encoding is equivalent to $P \ne NP$. -/
@[category research open, AMS 5 68]
theorem degreeFourThreeColorable_not_polytime :
    ¬ HasPolyTimeDecider DegreeFourThreeColorable := by
  sorry

/-- **SUBCUBIC VERTEX COVER** (Garey–Johnson–Stockmeyer, Theorem 2.6 and appendix p. 267).
Input: a square, symmetric, loopless Boolean adjacency matrix of maximum degree at most three
and a positive binary integer $k$. Property: at most $k$ vertices meet every edge. The degree
bound is not an exact regularity requirement. This problem is NP-complete, so the nonexistence
of a deterministic polynomial-time decider is equivalent to $P \ne NP$. -/
@[category research open, AMS 5 68]
theorem subcubicVertexCover_not_polytime : ¬ HasPolyTimeDecider SubcubicVertexCover := by
  sorry

/-- **CUBIC EDGE 3-COLORABILITY** (Holyer, §4). Input: a square, symmetric, loopless
Boolean adjacency matrix with every vertex of degree exactly three. Property: the unordered
edges can be colored with three colors so that incident edges have different colors.
No planarity restriction is imposed; the empty graph accepts by vacuous regularity.
This problem is NP-complete, so the nonexistence of a deterministic polynomial-time decider
for its binary encoding is equivalent to $P \ne NP$. -/
@[category research open, AMS 5 68]
theorem cubicEdgeThreeColorable_not_polytime :
    ¬ HasPolyTimeDecider CubicEdgeThreeColorable := by
  sorry

/-- **CUBIC HAMILTONIAN CIRCUIT** (Garey–Johnson–Tarjan, pp. 704–705).
Input: a square, symmetric, loopless Boolean adjacency matrix with every vertex of degree
exactly three. Property: a cycle of length at least three visits every vertex exactly once.
No planarity or connectivity restriction is imposed. This problem is NP-complete, so the
nonexistence of a deterministic polynomial-time decider for its binary encoding is equivalent
to $P \ne NP$. -/
@[category research open, AMS 5 68]
theorem cubicHamiltonian_not_polytime : ¬ HasPolyTimeDecider CubicHamiltonian := by
  sorry

/-- **CUBIC TWO-COLORABLE PERFECT MATCHING** (Schaefer, p. 217;
Demaine–Karntikoon–Pitimanaaree, Theorem 3). Input: a square, symmetric, loopless Boolean
adjacency matrix with every vertex of degree exactly three. Property: one two-coloring gives
each vertex exactly one neighbor of its own color. No planarity or connectivity restriction
is imposed; the empty graph accepts. This problem is NP-complete, so the nonexistence of a
deterministic polynomial-time decider for its binary encoding is equivalent to $P \ne NP$. -/
@[category research open, AMS 5 68]
theorem cubicTwoColorMatching_not_polytime : ¬ HasPolyTimeDecider CubicTwoColorMatching := by
  sorry

end BoundedDegreeComplexity
