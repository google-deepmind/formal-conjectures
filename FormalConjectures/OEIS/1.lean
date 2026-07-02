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

/-!
# Surjectivity of the group number function (A000001)

The number of groups of order $n$, $\mathrm{gnu}(n)$, is the OEIS sequence
[A000001](https://oeis.org/A000001). Conway, Dietrich and O'Brien conjecture (Conjecture 8.1)
that this function is surjective, i.e. every natural number arises as the number of groups
of some order.

*References:*
- [A000001](https://oeis.org/A000001)
- Conway, J. H., Dietrich, H., & O'Brien, E. A. (2008). Counting groups: Gnus, moas, and other
  exotica. The Mathematical Intelligencer, 30(2), 6–15.
  [doi:10.1007/BF02985731](https://doi.org/10.1007/BF02985731)
  ([pdf](https://www.math.auckland.ac.nz/~obrien/research/gnu.pdf))
-/

open GroupNumberFunction

namespace OeisA1

/--
The group number function `groupNumber` is surjective: every natural number is the number of
groups of some order. This is Conjecture 8.1 of Conway, Dietrich and O'Brien.

(The value $\mathrm{gnu}(0)$ is not considered in the paper, but the OEIS convention is
`groupNumber 0 = 0`.)
-/
@[category research open, AMS 20]
theorem groupNumber_surjective : Function.Surjective groupNumber := by
  sorry

/--
A stronger conjecture, credited to R. Keith Dennis, that every natural number is the number
of groups of order $n$ for some squarefree $n$.
-/
@[category research open, AMS 20]
theorem groupNumber_exists_squarefree : ∀ y, ∃ x : ℕ, Squarefree x ∧ groupNumber x = y := by
  sorry

/--
Dennis' squarefree conjecture (`groupNumber_exists_squarefree`) implies surjectivity of
`groupNumber`.
-/
@[category API, AMS 20]
theorem groupNumber_surjective_of_exists_squarefree
    (h : ∀ y, ∃ x : ℕ, Squarefree x ∧ groupNumber x = y) : Function.Surjective groupNumber := by
  intro y
  grind [h y]

end OeisA1
