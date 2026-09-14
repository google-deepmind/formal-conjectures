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
# Exact Euclidean travelling salesman and rectilinear Steiner trees

*References:*
- Garey and Johnson, *Computers and Intractability* (1979), ND13 (p. 209) and
  ND23 (p. 212), including their metric-variant comments.
  https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf
- Garey and Johnson, *The Rectilinear Steiner Tree Problem is NP-Complete*,
  SIAM Journal on Applied Mathematics 32(4) (1977), 826–834, §§1–3.
  https://doi.org/10.1137/0132071
- Garey, Graham, and Johnson, *Some NP-complete geometric problems*, STOC 1976, 10–22.
  https://doi.org/10.1145/800113.803626
-/

namespace GareyJohnson1979

open ComplexityTheory Computability.GeometricProblems

/-- **EXACT EUCLIDEAN TRAVELLING SALESMAN** (ND23, p. 212, non-discretized variant).
Input: a duplicate-free list of integer-coordinate plane points and a positive integer
budget $B$, all binary encoded. Property: a permutation tour through all points, including
its return edge, has exact Euclidean length at most $B$. Distances are not rounded;
empty and singleton tours cost zero. This problem is NP-hard but not known to be in NP.
Thus $P\ne NP$ implies the nonexistence of a deterministic polynomial-time decider;
the converse is not known. -/
@[category research open, AMS 52 68]
theorem euclideanTravelingSalesman_not_polytime :
    ¬ HasPolyTimeDecider EuclideanTravelingSalesman := by
  sorry

/-- **RECTILINEAR STEINER TREE** (ND13, p. 209; Garey–Johnson 1977).
Input: a duplicate-free list of integer-coordinate terminals and a positive integer budget
$B$, all binary encoded. Property: a finite tree on integer-coordinate points contains all
terminals and has total Manhattan edge length at most $B$, counting each undirected edge
once. Additional Steiner points are unrestricted; empty terminals permit a singleton tree.
This problem is NP-complete, so the nonexistence of a deterministic polynomial-time decider
is equivalent to $P \ne NP$. -/
@[category research open, AMS 5 52 68]
theorem rectilinearSteinerTree_not_polytime :
    ¬ HasPolyTimeDecider RectilinearSteinerTree := by
  sorry

end GareyJohnson1979
