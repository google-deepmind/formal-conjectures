/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjectures.Util.ProblemImports

/-!
# Rational distance problem

*Reference:* (https://en.wikipedia.org/wiki/Unit_square#Rational_distance_problem)

*Reference* (https://mathoverflow.net/questions/418260)
-/

namespace RationalDistanceProblem

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def UnitSquareCorners : Fin 4 → Plane :=
  ![![0, 0], ![1, 0], ![1, 1], ![0, 1]]

/-
Does there exist a point in the plane at rational distance from all four vertices of the unit square?
-/
@[category research open, AMS 11 51]
theorem rational_distance_problem :
  ∃ P : Plane, ∀ i, ¬ Irrational (dist P (UnitSquareCorners i)) ↔ answer(sorry) := by
    sorry

end RationalDistanceProblem
