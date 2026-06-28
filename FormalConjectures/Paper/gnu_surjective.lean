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
import FormalConjectures.Paper.gnu

/-!
# The conjecture that the function `gnu` is surjective. This is conjecture 8.1 in the following paper:

*Reference:*
- Conway, J. H., Dietrich, H., & O'Brien, E. A. (2008). Counting groups: Gnus, moas, and other exotica. The Mathematical Intelligencer, 30(2), 6–15. https://doi.org/10.1007/BF02985731 (https://www.math.auckland.ac.nz/~obrien/research/gnu.pdf)
-/
namespace GrpOfOrder

/--
The function `gnu` is surjective.

This is equivalent to the statement ∀ y, ∃ x : ℕ, gnu x = y.

(The case of `gnu 0` is not considered in the paper, but the OEIS convention is gnu 0 = 0.)
-/
@[category research open, AMS 20]
theorem gnu_surjective : Function.Surjective gnu := by
  sorry

/--
A stronger conjecture, credited to R. Keith Dennis, that every number is the value of gnu n for some square-free n.
-/
@[category research open, AMS 20]
theorem gnu_exists_squarefree : ∀ y, ∃ x : ℕ, Squarefree x ∧ gnu x = y := by
  sorry

@[category API, AMS 20]
example (h : ∀ y, ∃ x : ℕ, Squarefree x ∧ gnu x = y) : Function.Surjective gnu := by
  intro y
  grind [h y]


end GrpOfOrder
