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
# Covering rational points by straight lines

Megiddo and Tamir, *On the complexity of locating linear facilities in the plane*,
Operations Research Letters 1(5) (1982), 194–197:
Point Covering (PC), p. 195, and the reduction and coordinate construction,
pp. 195–197. Rational numerators and denominators are explicitly represented.
https://doi.org/10.1016/0167-6377(82)90039-6
https://theory.stanford.edu/~megiddo/pdf/complexity%20of%20locating%20linear%20facilities.pdf

Langerman and Morin, *Covering Points with Lines*, §1, studies the decision
problem with the number of lines as a parameter.
https://cglab.ca/~morin/publications/fpt/linecover-fw.pdf

The budget is part of the binary-encoded input, not a fixed constant.
The covering lines have arbitrary real coefficients and nonzero normals;
they need not be supplied with the input or belong to a predetermined list.
The existential family may repeat lines, so it expresses an upper bound.
This is PC in the original paper, not its dual problem called Line Covering (LC).
The paper proves NP-hardness; the open statement below is the associated
polynomial-time lower-bound conjecture. No reduction is formally proved here.
-/

namespace MegiddoTamir1982

open ComplexityTheory Computability.GeometricProblems

/-- No deterministic polynomial-time decider for whether a finite set of
rational points can be covered by at most an input number of straight lines. -/
@[category research open, AMS 52 68]
theorem lineCover_not_polytime : ¬ HasPolyTimeDecider LineCover := by
  sorry

end MegiddoTamir1982
