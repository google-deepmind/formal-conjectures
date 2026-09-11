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
# Feedback sets, Steiner trees, travelling salesman and disjoint paths

*References:*
- Garey and Johnson, *Computers and Intractability* (W. H. Freeman, 1979),
  GT7–GT8 (pp. 191–192), ND12 (pp. 208–209), ND22 (p. 211), and ND40 (p. 217).
  https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf
- Karp, *Reducibility among Combinatorial Problems* (1972), Main Theorem,
  items 7–8, 10, 16 and reductions on pp. 98–99.
  https://doi.org/10.1007/978-1-4684-2001-2_9
- J. F. Lynch, *The equivalence of theorem proving and the interconnection problem*,
  ACM SIGDA Newsletter 5(3) (1975), pp. 31–36, Theorem I (pp. 32–33).
  https://doi.org/10.1145/1061425.1061430
- Robertson and Seymour, *Graph Minors XIII. The Disjoint Paths Problem*,
  Journal of Combinatorial Theory, Series B 63 (1995), pp. 65–110.
  https://doi.org/10.1006/jctb.1995.1006
-/

namespace GareyJohnson1979

open ComplexityTheory Computability.NetworkProblems

/-- **FEEDBACK VERTEX SET** (GT7, p. 191). Input: a square, loopless Boolean adjacency
matrix of a digraph $G=(V,A)$ and a binary integer $0<k\le |V|$. Property: at most $k$
vertices meet every directed cycle, including cycles of length two. This problem is
NP-complete, so the nonexistence of a deterministic polynomial-time decider is equivalent
to $P \ne NP$. -/
@[category research open, AMS 5 68]
theorem feedbackVertexSet_not_polytime : ¬ HasPolyTimeDecider FeedbackVertexSet := by
  sorry

/-- **FEEDBACK ARC SET** (GT8, p. 192). Input: a square, loopless Boolean adjacency
matrix of a digraph $G=(V,A)$ and a binary integer $0<k\le |A|$. Property: at most $k$
actual directed arcs meet every directed cycle, including cycles of length two.
This problem is NP-complete, so the nonexistence of a deterministic polynomial-time decider
is equivalent to $P \ne NP$. -/
@[category research open, AMS 5 68]
theorem feedbackArcSet_not_polytime : ¬ HasPolyTimeDecider FeedbackArcSet := by
  sorry

/-- **STEINER TREE IN GRAPHS** (ND12, pp. 208–209). Input: a square, symmetric, loopless
Boolean adjacency matrix, a symmetric matrix of nonnegative binary integer edge weights,
a terminal mask and a positive binary budget $B$. Property: a nonempty tree in the graph
contains all terminals and has total edge weight at most $B$, counting each edge once.
Additional nonterminal vertices are allowed; a singleton is a zero-cost tree. This problem
is NP-complete, so the nonexistence of a deterministic polynomial-time decider is equivalent
to $P \ne NP$. -/
@[category research open, AMS 5 68 90]
theorem steinerTree_not_polytime : ¬ HasPolyTimeDecider SteinerTree := by
  sorry

/-- **SYMMETRIC TRAVELLING SALESMAN** (ND22, p. 211). Input: a square, symmetric matrix
of binary integer distances, zero on the diagonal and positive elsewhere, and a positive
binary budget $B$. Property: a permutation of the cities, including its return leg, costs
at most $B$. No triangle inequality is assumed. Empty and singleton tours cost zero;
two-city tours pay in both directions. This problem is NP-complete, so the nonexistence of
a deterministic polynomial-time decider is equivalent to $P \ne NP$. -/
@[category research open, AMS 5 68 90]
theorem travelingSalesman_not_polytime : ¬ HasPolyTimeDecider TravelingSalesman := by
  sorry

/-- **DISJOINT CONNECTING PATHS** (ND40, p. 217; Lynch, Theorem I). Input: a square,
symmetric, loopless Boolean adjacency matrix and a list of terminal pairs with binary
vertex indices, all in range and mutually distinct. Property: simultaneous vertex-disjoint
paths connect the respective pairs. The number of pairs is part of the input, not a fixed
parameter; an empty list accepts. No planarity restriction is imposed. This problem is
NP-complete, so the nonexistence of a deterministic polynomial-time decider is equivalent
to $P \ne NP$. -/
@[category research open, AMS 5 68 90]
theorem disjointConnectingPaths_not_polytime : ¬ HasPolyTimeDecider DisjointConnectingPaths := by
  sorry

end GareyJohnson1979
