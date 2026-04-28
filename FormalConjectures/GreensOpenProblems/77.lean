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

import FormalConjectures.Util.ProblemImports
import FormalConjectures.ErdosProblems.«507»

/-!
# Ben Green's Open Problem 77

*Reference:*
- [Ben Green's Open Problem 77](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.77)
-/

open Erdos507 Filter Topology

namespace Green77

/--
Given $n$ points in the unit disc, must there be a triangle of area at most $n^{-2+o(1)}$
determined by them?
-/
@[category research open, AMS 5 52]
theorem green_77 :
    answer(sorry) ↔
    ∃ (o : ℕ → ℝ), Tendsto o atTop (𝓝 0) ∧
      α ≪ fun n ↦ n ^ (-2 + o n) := by
  sorry

end Green77
