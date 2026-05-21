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

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Unit_square#Rational_distance_problem)
- [mathoverflow/418260](https://mathoverflow.net/questions/418260/)
asked by user [Yuan Yang](https://mathoverflow.net/users/177957/yuan-yang)
- D19 in [Unsolved Problems in Number Theory](https://doi.org/10.1007/978-0-387-26677-0)
by *Richard K. Guy*
-/

namespace RationalDistanceProblem

open EuclideanGeometry

def UnitSquareCorners : Fin 4 → ℝ² :=
  ![!₂[0, 0], !₂[1, 0], !₂[1, 1], !₂[0, 1]]

/--
Does there exist a point in the plane at rational distance from all four vertices of the unit square?
-/
@[category research open, AMS 11 51]
theorem rational_distance_problem :
    answer(sorry) ↔ ∃ P : ℝ² , ∀ i, ¬ Irrational (dist P (UnitSquareCorners i)) := by
  sorry

end RationalDistanceProblem
