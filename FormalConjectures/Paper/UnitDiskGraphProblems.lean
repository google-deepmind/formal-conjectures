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

*References:*
- Clark, Colbourn, and Johnson, *Unit disk graphs*, Discrete Mathematics 86 (1990),
  165–177, §1 (pp. 165–167), Theorem 4.1 (pp. 171–172), and Theorem 5.1 (pp. 172–173).
  https://doi.org/10.1016/0012-365X(90)90358-O
  https://cs.du.edu/~snarayan/sada/research/docs/res/unitdisk.pdf
-/

namespace ClarkColbournJohnson1990

open ComplexityTheory Computability.GeometricProblems

/-- **UNIT-DISK INDEPENDENT SET** (Clark–Colbourn–Johnson, §4, Theorem 4.1).
Input: distinct rational plane centers, a positive rational proximity threshold $d$ and
a nonnegative integer $K$, all binary encoded. Property: at least $K$ input centers have
pairwise Euclidean distances strictly greater than $d$. The represented graph uses
distance at most $d$ for adjacency; $d$ is a disk diameter, not a radius. This problem is
NP-complete, so the nonexistence of a deterministic polynomial-time decider is equivalent
to $P \ne NP$. -/
@[category research open, AMS 5 52 68]
theorem unitDiskIndependentSet_not_polytime :
    ¬ HasPolyTimeDecider UnitDiskIndependentSet := by
  sorry

/-- **UNIT-DISK DOMINATING SET** (Clark–Colbourn–Johnson, §5, Theorem 5.1).
Input: distinct rational plane centers, a positive rational proximity threshold $d$ and
a nonnegative integer $K$, all binary encoded. Property: at most $K$ input centers can be
selected so that every input center is at Euclidean distance at most $d$ from a selected
center. Selection is restricted to the input and includes self-coverage. This problem is
NP-complete, so the nonexistence of a deterministic polynomial-time decider is equivalent
to $P \ne NP$. -/
@[category research open, AMS 5 52 68]
theorem unitDiskDominatingSet_not_polytime :
    ¬ HasPolyTimeDecider UnitDiskDominatingSet := by
  sorry

end ClarkColbournJohnson1990
