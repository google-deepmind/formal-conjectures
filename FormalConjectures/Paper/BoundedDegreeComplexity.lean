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
# Five bounded-degree formulations of P versus NP

These conjecture the nonexistence of deterministic polynomial-time deciders for five
restricted graph problems. Graphs are explicit Boolean adjacency matrices. Cubic means
every vertex has degree exactly three, not merely at most three.

References:
- Garey, Johnson, and Stockmeyer, *Some simplified NP-complete graph problems*,
  Theoretical Computer Science 1 (1976), pp. 237–267,
  https://doi.org/10.1016/0304-3975(76)90059-1.
  Theorem 2.3 (pp. 251–252) gives degree-four 3-colorability hardness, even for planar
  graphs; Theorem 2.6 (pp. 260–262) gives vertex-cover hardness with maximum degree three.
- Holyer, *The NP-Completeness of Edge-Coloring*, SIAM Journal on Computing 10 (1981),
  pp. 718–720, https://doi.org/10.1137/0210055, §4, gives cubic edge-coloring hardness.
- Garey, Johnson, and Tarjan, *The Planar Hamiltonian Circuit Problem is NP-Complete*,
  SIAM Journal on Computing 5 (1976), pp. 704–714, https://doi.org/10.1137/0205049,
  pp. 704–705, establishes hardness even for planar, triply-connected cubic graphs.
- Schaefer, *The Complexity of Satisfiability Problems*, STOC (1978), pp. 216–226,
  https://doi.org/10.1145/800133.804350, p. 217 and Theorem 7.1 / its comment on p. 225,
  gives two-colorable perfect-matching hardness, including the cubic restriction.
- Demaine, Karntikoon, and Pitimanaaree, *2-Colorable Perfect Matching is NP-complete in
  2-Connected 3-Regular Planar Graphs*, Theory of Computing Systems 69, article 22 (2025),
  https://doi.org/10.1007/s00224-025-10221-2, Theorem 3, supplies the proof omitted by
  Schaefer for the planar-cubic restriction and strengthens it to 2-connected graphs.

No planarity or connectivity condition is imposed here. The stronger restricted results
supply classical hardness background, not formalized reductions or an equivalence to
$P \ne NP$.
-/

namespace BoundedDegreeComplexity

open ComplexityTheory Computability.MatrixGraph

/-- No polynomial-time decider for proper vertex 3-colorability among simple graphs of
maximum degree at most four (Garey–Johnson–Stockmeyer, Theorem 2.3). -/
@[category research open, AMS 5 68]
theorem degreeFourThreeColorable_not_polytime :
    ¬ HasPolyTimeDecider DegreeFourThreeColorable := by
  sorry

/-- No polynomial-time decider for a vertex cover of size at most a positive input bound
in a simple graph of maximum degree at most three (Garey–Johnson–Stockmeyer, Theorem 2.6). -/
@[category research open, AMS 5 68]
theorem subcubicVertexCover_not_polytime : ¬ HasPolyTimeDecider SubcubicVertexCover := by
  sorry

/-- No polynomial-time decider for proper edge 3-colorability among cubic simple graphs
(Holyer, §4). -/
@[category research open, AMS 5 68]
theorem cubicEdgeThreeColorable_not_polytime :
    ¬ HasPolyTimeDecider CubicEdgeThreeColorable := by
  sorry

/-- No polynomial-time decider for Hamiltonian cycles among cubic simple graphs
(Garey–Johnson–Tarjan, pp. 704–705). -/
@[category research open, AMS 5 68]
theorem cubicHamiltonian_not_polytime : ¬ HasPolyTimeDecider CubicHamiltonian := by
  sorry

/-- No polynomial-time decider for coloring a cubic simple graph with two colors so that
each vertex has exactly one neighbor of its own color (Schaefer, p. 217;
Demaine–Karntikoon–Pitimanaaree, Theorem 3). -/
@[category research open, AMS 5 68]
theorem cubicTwoColorMatching_not_polytime : ¬ HasPolyTimeDecider CubicTwoColorMatching := by
  sorry

end BoundedDegreeComplexity
