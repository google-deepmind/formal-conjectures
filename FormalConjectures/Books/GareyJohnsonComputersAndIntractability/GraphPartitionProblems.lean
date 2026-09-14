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
# Graph partitions, balanced bicliques and size-constrained cuts

*References:*
- Garey and Johnson, *Computers and Intractability* (Freeman, 1979),
  GT11 (p. 192), GT15 (p. 193), GT24 (p. 196), ND14 (p. 209), ND17 (p. 210),
  and Theorem 3.7 (pp. 68–69).
  https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf
- Karp, *Reducibility among Combinatorial Problems* (1972), item 13 (p. 95),
  and the clique-cover reduction (p. 99).
  https://doi.org/10.1007/978-1-4684-2001-2_9
- Hyafil and Rivest, *Graph Partitioning and Constructing Optimal Decision Trees are
  Polynomial Complete Problems*, IRIA report 33 (1973), pp. 2–5.
  https://people.csail.mit.edu/rivest/pubs/HR73.pdf
- Garey, Johnson, and Stockmeyer, *Some simplified NP-complete graph problems*,
  TCS 1 (1976), Theorem 1.3 (pp. 242–243).
  https://doi.org/10.1016/0304-3975(76)90059-1
-/

namespace GareyJohnson1979

open ComplexityTheory Computability.GraphPartitionProblems

/-- **PARTITION INTO CLIQUES** (GT15, p. 193). Input: a square, symmetric, loopless
Boolean adjacency matrix of $G=(V,E)$ and a binary integer $0<k\le |V|$.
Property: $V$ can be partitioned into at most $k$ nonempty cliques. Every vertex belongs
to exactly one part. This problem is NP-complete, so the nonexistence of a deterministic
polynomial-time decider is equivalent to $P \ne NP$. -/
@[category research open, AMS 5 68]
theorem cliquePartition_not_polytime : ¬ HasPolyTimeDecider CliquePartition := by
  sorry

/-- **PARTITION INTO TRIANGLES** (GT11, p. 192; Theorem 3.7, pp. 68–69).
Input: a square, symmetric, loopless Boolean adjacency matrix with $3q$ vertices for
a positive integer $q$. Property: $q$ vertex-disjoint triangles cover every vertex.
The empty graph rejects, following Theorem 3.7. This problem is NP-complete, so the
nonexistence of a deterministic polynomial-time decider for its binary encoding is
equivalent to $P \ne NP$. -/
@[category research open, AMS 5 68]
theorem trianglePartition_not_polytime : ¬ HasPolyTimeDecider TrianglePartition := by
  sorry

/-- **BALANCED COMPLETE BIPARTITE SUBGRAPH** (GT24, p. 196). Input: a square, symmetric,
loopless Boolean adjacency matrix of a bipartite graph $G=(V,E)$ and a binary integer
$0<k\le |V|$. Property: two disjoint sets of exactly $k$ vertices each have every cross
edge present. Equal side sizes are required, not merely a total-size bound. This problem
is NP-complete, so the nonexistence of a deterministic polynomial-time decider is equivalent
to $P \ne NP$. -/
@[category research open, AMS 5 68]
theorem balancedBiclique_not_polytime : ¬ HasPolyTimeDecider BalancedBiclique := by
  sorry

/-- **GRAPH PARTITIONING** (ND14, p. 209). Input: a square, symmetric, loopless Boolean
adjacency matrix, positive binary integer vertex and edge weights, a positive capacity $K$
and a positive budget $J$. Property: a partition of all vertices has vertex-weight sum
at most $K$ in each part and total crossing-edge weight at most $J$, counting each edge
once. The number of parts is unrestricted, and parts need not be connected. This problem
is NP-complete, so the nonexistence of a deterministic polynomial-time decider is equivalent
to $P \ne NP$. -/
@[category research open, AMS 5 68 90]
theorem weightedPartition_not_polytime : ¬ HasPolyTimeDecider WeightedPartition := by
  sorry

/-- **MINIMUM CUT INTO BOUNDED SETS** (ND17, p. 210). Input: a square, symmetric,
loopless Boolean adjacency matrix of $G=(V,E)$, positive binary integer edge weights,
terminal indices $s,t\in V$, a binary bound $0<B\le |V|$ and a positive binary budget $K$.
Property: a partition $V=V_1\sqcup V_2$ has $s\in V_1$, $t\in V_2$, both side sizes
at most $B$, and total crossing-edge weight at most $K$, counting each edge once.
Coincident terminals cannot be separated. This problem is NP-complete, so the nonexistence
of a deterministic polynomial-time decider is equivalent to $P \ne NP$. -/
@[category research open, AMS 5 68 90]
theorem boundedCut_not_polytime : ¬ HasPolyTimeDecider BoundedCut := by
  sorry

end GareyJohnson1979
