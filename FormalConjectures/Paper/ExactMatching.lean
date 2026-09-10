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
# Exact matching in general graphs

*References:*
* El Maalouly, *Exact Matching: Algorithms and Related Problems*, STACS 2023,
  §1, pp. 29:1–29:3, https://doi.org/10.4230/LIPIcs.STACS.2023.29.
-/

namespace ElMaalouly2023

/-- **Exact Matching** (El Maalouly, §1, task box p. 29:1): is there a deterministic
polynomial bit-time decider for a perfect matching with exactly $k$ red edges?
Input: a loopless undirected graph and its red-edge subset as explicit symmetric
Boolean matrices, and a signed binary integer $k$; other edges are blue. Malformed
matrices and negative targets are rejected. The empty graph accepts exactly $k=0$.
No bipartiteness, planarity or density restriction is imposed. This remains a
two-sided derandomization question for a problem in $RP$, so $P=RP$ would imply
a positive answer; it is not arbitrary binary-weight Exact Matching. -/
@[category research open, AMS 5 68]
theorem exactMatching_polytime : answer(sorry) ↔
    ComplexityTheory.HasPolyTimeDecider Computability.MatrixGraph.ExactMatching := by
  sorry

end ElMaalouly2023
