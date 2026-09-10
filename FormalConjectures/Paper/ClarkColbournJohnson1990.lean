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
# Independent and dominating sets in represented unit-disk graphs

Clark, Colbourn, and Johnson, *Unit disk graphs*, Discrete Mathematics 86 (1990),
165–177. The proximity model is defined in §1, pp. 165–167. Theorem 4.1 and
the preceding complement observation, pp. 171–172, establish independent-set
hardness; §5 and Theorem 5.1, pp. 172–173, establish domination hardness even
for grid graphs.
https://doi.org/10.1016/0012-365X(90)90358-O
https://cs.du.edu/~snarayan/sada/research/docs/res/unitdisk.pdf

Inputs provide rational centers, a positive rational proximity threshold,
and a cardinality bound. The threshold is the disk diameter in the intersection
model, not its radius. Distance equality counts as adjacency.
The graph representation is given; no recognition problem is being asserted.
Rational coordinates are essential: independent set is polynomial-time solvable
for the integer-grid, threshold-one subclass discussed in the same paper.
Domination selects centers from the input and includes self-coverage.

The paper supplies NP-completeness results and geometric constructions.
The statements below conjecture the absence of polynomial-time deciders in
the existing binary TM2 model. No hardness reduction or equivalence to
$P \ne NP$ is formally proved here.
-/

namespace ClarkColbournJohnson1990

open ComplexityTheory Computability.GeometricProblems

/-- No deterministic polynomial-time decider for an independent set of at least
an input number of vertices in a rationally represented unit-disk graph. -/
@[category research open, AMS 5 52 68]
theorem unitDiskIndependentSet_not_polytime :
    ¬ HasPolyTimeDecider UnitDiskIndependentSet := by
  sorry

/-- No deterministic polynomial-time decider for a dominating set of at most
an input number of vertices in a rationally represented unit-disk graph. -/
@[category research open, AMS 5 52 68]
theorem unitDiskDominatingSet_not_polytime :
    ¬ HasPolyTimeDecider UnitDiskDominatingSet := by
  sorry

end ClarkColbournJohnson1990
