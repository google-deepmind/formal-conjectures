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
# Five graph formulations of P versus NP

These are the conjectured nonexistence of polynomial-time deciders for five classical
NP-complete problems, using explicit adjacency matrices and binary integer parameters.
Karp's completeness theorem and Theorem 3 explain their relation to $P \ne NP$.
The completeness reductions themselves are not proved in this file.

*Reference:* Richard M. Karp, *Reducibility among Combinatorial Problems*, in
*Complexity of Computer Computations* (1972), pp. 85–103,
https://doi.org/10.1007/978-1-4684-2001-2_9.
See §4, Theorem 3 (p. 93), and Main Theorem items 3, 5, 9, 10, 12 (pp. 94–95).
-/

namespace Karp1972

open ComplexityTheory Computability.MatrixGraph

/-- No polynomial-time decider for CLIQUE (item 3, p. 94). -/
@[category research open, AMS 5 68]
theorem clique_not_polytime : ¬ HasPolyTimeDecider Clique := by
  sorry

/-- No polynomial-time decider for NODE COVER, now called vertex cover (item 5, p. 94). -/
@[category research open, AMS 5 68]
theorem vertexCover_not_polytime : ¬ HasPolyTimeDecider VertexCover := by
  sorry

/-- No polynomial-time decider for CHROMATIC NUMBER with the color bound in the input
(item 12, p. 95). -/
@[category research open, AMS 5 68]
theorem colorable_not_polytime : ¬ HasPolyTimeDecider Colorable := by
  sorry

/-- No polynomial-time decider for DIRECTED HAMILTON CIRCUIT (item 9, p. 94). -/
@[category research open, AMS 5 68]
theorem directedHamiltonian_not_polytime : ¬ HasPolyTimeDecider DirectedHamiltonian := by
  sorry

/-- No polynomial-time decider for UNDIRECTED HAMILTON CIRCUIT (item 10, p. 94). -/
@[category research open, AMS 5 68]
theorem undirectedHamiltonian_not_polytime : ¬ HasPolyTimeDecider UndirectedHamiltonian := by
  sorry

end Karp1972
