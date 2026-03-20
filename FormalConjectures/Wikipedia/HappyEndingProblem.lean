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
import FormalConjectures.ErdosProblems.«107»

/-!
# Happy Ending Problem

The happy ending problem asks whether $f(n) = 2^{n-2} + 1$, where $f(n)$ is the
smallest number such that any $f(n)$ points in general position in the plane
contain $n$ that form a convex polygon.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Happy_ending_problem)

This file points to the canonical formalization in `FormalConjectures.ErdosProblems.«107»`.
-/

namespace HappyEndingProblem

/--
This Wikipedia entry points to the canonical formalization of the happy ending
problem in `FormalConjectures.ErdosProblems.«107»`.
-/
@[category research open, AMS 52]
theorem happy_ending_problem : type_of% @Erdos107.erdos_107 := by
  sorry

end HappyEndingProblem
