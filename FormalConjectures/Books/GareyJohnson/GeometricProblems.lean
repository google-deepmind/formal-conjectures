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
# Geometric polynomial-time lower-bound formulations

Garey and Johnson, *Computers and Intractability* (1979), ND13 (p. 209) and
ND23 (p. 212), including their metric-variant comments.
https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf

Garey and Johnson, *The Rectilinear Steiner Tree Problem is NP-Complete*,
SIAM Journal on Applied Mathematics 32(4) (1977), 826–834, §§1–3, supplies
the integer-input Steiner problem and its NP-completeness.
https://doi.org/10.1137/0132071

Garey, Graham, and Johnson, *Some NP-complete geometric problems*, STOC 1976,
10–22, is ND23's reference for exact Euclidean TSP hardness.
https://doi.org/10.1145/800113.803626

The TSP statement uses exact Euclidean lengths, without rounding. ND23 distinguishes
this NP-hard variant from discretized Euclidean TSP, which is NP-complete.
No NP-membership assertion for the exact variant is made here.
The Steiner statement uses unrestricted finite integer Steiner-point sets,
actual Mathlib trees, and Manhattan edge weights counted once per undirected edge.
These are geometric restrictions, not the arbitrary weighted-graph inputs of
ND12 and ND22. The conjectured lower bounds use the existing binary TM2 model;
no hardness reduction or complexity-class equivalence is formally proved here.
-/

namespace GareyJohnson1979

open ComplexityTheory Computability.GeometricProblems

/-- No deterministic polynomial-time decider for an exact Euclidean tour through
integer-coordinate points of length at most a positive integer input budget. -/
@[category research open, AMS 52 68]
theorem euclideanTravelingSalesman_not_polytime :
    ¬ HasPolyTimeDecider EuclideanTravelingSalesman := by
  sorry

/-- No deterministic polynomial-time decider for a rectilinear Steiner tree
on integer-coordinate terminals of total length at most a positive input budget. -/
@[category research open, AMS 5 52 68]
theorem rectilinearSteinerTree_not_polytime :
    ¬ HasPolyTimeDecider RectilinearSteinerTree := by
  sorry

end GareyJohnson1979
