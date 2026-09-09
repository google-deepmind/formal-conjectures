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
# Five graph-partition formulations of P versus NP

Each statement conjectures that an encoded finite decision problem has no uniform
deterministic polynomial-time decider, using the existing TM2 model and binary encodings.

Primary reference: Garey and Johnson, *Computers and Intractability* (Freeman, 1979),
GT11 (p. 192), GT15 (p. 193), GT24 (p. 196), ND14 (p. 209), ND17 (p. 210).
Triangle partition follows the positive-size convention of Theorem 3.7 (pp. 68–69).
https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf

Original hardness background:
- Karp, *Reducibility among Combinatorial Problems* (1972), item 13 (p. 95),
  and the clique-cover reduction (p. 99).
  https://doi.org/10.1007/978-1-4684-2001-2_9
- Hyafil and Rivest, *Graph Partitioning and Constructing Optimal Decision Trees are
  Polynomial Complete Problems*, IRIA report 33 (1973), pp. 2–5. The weighted
  generalization is discussed on p. 3.
  https://people.csail.mit.edu/rivest/pubs/HR73.pdf
- Garey, Johnson, and Stockmeyer, *Some simplified NP-complete graph problems*,
  TCS 1 (1976), Theorem 1.3 (pp. 242–243): equal-size terminal-separating cuts,
  the unit-weight special case of ND17.
  https://doi.org/10.1016/0304-3975(76)90059-1

GT24 requires a bipartite input and equal biclique side sizes, not just a bound on their
total size. ND14 permits any number of parts. ND17 bounds both sides of a terminal cut;
it is not ordinary minimum cut without size constraints.

These are lower-bound conjectures. No NP-completeness reduction or equivalence to
$P \ne NP$ is formally proved here.
-/

namespace GareyJohnson1979

open ComplexityTheory Computability.GraphPartitionProblems

/-- No polynomial-time decider for GT15: partitioning a graph into at most a positive
input number of cliques, with that bound at most the vertex count. -/
@[category research open, AMS 5 68]
theorem cliquePartition_not_polytime : ¬ HasPolyTimeDecider CliquePartition := by
  sorry

/-- No polynomial-time decider for GT11: partitioning a nonempty graph of order $3q$
into $q$ vertex-disjoint triangles covering every vertex. -/
@[category research open, AMS 5 68]
theorem trianglePartition_not_polytime : ¬ HasPolyTimeDecider TrianglePartition := by
  sorry

/-- No polynomial-time decider for GT24: finding a balanced complete bipartite subgraph
with a positive input number of vertices on each side, in a bipartite input graph. -/
@[category research open, AMS 5 68]
theorem balancedBiclique_not_polytime : ¬ HasPolyTimeDecider BalancedBiclique := by
  sorry

/-- No polynomial-time decider for ND14: partitioning a positively weighted graph
subject to a positive vertex-weight capacity per part and a positive crossing-edge budget. -/
@[category research open, AMS 5 68 90]
theorem weightedPartition_not_polytime : ¬ HasPolyTimeDecider WeightedPartition := by
  sorry

/-- No polynomial-time decider for ND17: a terminal-separating cut with both side sizes
bounded by a positive input bound, positive edge weights, and a positive cost budget. -/
@[category research open, AMS 5 68 90]
theorem boundedCut_not_polytime : ¬ HasPolyTimeDecider BoundedCut := by
  sorry

end GareyJohnson1979
