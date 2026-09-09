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
# Five network-design formulations of P versus NP

Each statement conjectures the absence of a uniform deterministic polynomial-time
decider for a finite network problem, using the existing TM2 model and binary encodings.

Primary statement reference: Garey and Johnson, *Computers and Intractability*
(W. H. Freeman, 1979), GT7–GT8 (pp. 191–192), ND12 (pp. 208–209), ND22 (p. 211),
and ND40 (p. 217).
https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf

Hardness background:
- Karp, *Reducibility among Combinatorial Problems* (1972), Main Theorem,
  items 7–8, 10, 16 and reductions on pp. 98–99.
  https://doi.org/10.1007/978-1-4684-2001-2_9
- J. F. Lynch, *The equivalence of theorem proving and the interconnection problem*,
  ACM SIGDA Newsletter 5(3) (1975), pp. 31–36, Theorem I (pp. 32–33).
  https://doi.org/10.1145/1061425.1061430

The path problem has an input-sized number of terminal pairs. Its fixed-size versions
have polynomial algorithms: Robertson and Seymour, *Graph Minors XIII* (1995).
https://doi.org/10.1006/jctb.1995.1006

These are lower-bound conjectures, not formalized NP-completeness reductions or
proved equivalences to $P \ne NP$. No planar restriction is imposed.
-/

namespace GareyJohnson1979

open ComplexityTheory Computability.NetworkProblems

/-- No polynomial-time decider for GT7: a directed feedback vertex set of size at most
a positive input bound, itself at most the vertex count. -/
@[category research open, AMS 5 68]
theorem feedbackVertexSet_not_polytime : ¬ HasPolyTimeDecider FeedbackVertexSet := by
  sorry

/-- No polynomial-time decider for GT8: a directed feedback arc set of size at most
a positive input bound, itself at most the arc count. -/
@[category research open, AMS 5 68]
theorem feedbackArcSet_not_polytime : ¬ HasPolyTimeDecider FeedbackArcSet := by
  sorry

/-- No polynomial-time decider for ND12: a tree containing specified terminals and
meeting a positive budget, with nonnegative integer edge weights. -/
@[category research open, AMS 5 68 90]
theorem steinerTree_not_polytime : ¬ HasPolyTimeDecider SteinerTree := by
  sorry

/-- No polynomial-time decider for ND22: a symmetric travelling-salesman tour within
a positive budget, with positive integer distances between distinct cities. -/
@[category research open, AMS 5 68 90]
theorem travelingSalesman_not_polytime : ¬ HasPolyTimeDecider TravelingSalesman := by
  sorry

/-- No polynomial-time decider for ND40: mutually vertex-disjoint paths connecting
each pair in an input-sized list of disjoint terminal pairs. -/
@[category research open, AMS 5 68 90]
theorem disjointConnectingPaths_not_polytime : ¬ HasPolyTimeDecider DisjointConnectingPaths := by
  sorry

end GareyJohnson1979
