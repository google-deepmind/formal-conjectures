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

*References:*
- Megiddo and Tamir, *On the complexity of locating linear facilities in the plane*,
  Operations Research Letters 1(5) (1982), 194–197, Point Covering (PC), pp. 195–197.
  https://doi.org/10.1016/0167-6377(82)90039-6
  https://theory.stanford.edu/~megiddo/pdf/complexity%20of%20locating%20linear%20facilities.pdf
- Langerman and Morin, *Covering Points with Lines*, §1.
  https://cglab.ca/~morin/publications/fpt/linecover-fw.pdf
-/

namespace MegiddoTamir1982

open ComplexityTheory Computability.GeometricProblems

/-- **POINT COVERING** (Megiddo–Tamir, PC, p. 195). Input: a duplicate-free list of
rational-coordinate plane points and a nonnegative line budget $K$, all binary encoded.
Property: at most $K$ arbitrary real affine lines cover the points. Every line has a nonzero
normal, and $K=0$ covers only the empty set. The budget is not fixed, and this is PC rather
than the paper's dual LC problem. This problem is NP-complete, so the nonexistence of a
deterministic polynomial-time decider is equivalent to $P \ne NP$. -/
@[category research open, AMS 52 68]
theorem lineCover_not_polytime : ¬ HasPolyTimeDecider LineCover := by
  sorry

end MegiddoTamir1982
