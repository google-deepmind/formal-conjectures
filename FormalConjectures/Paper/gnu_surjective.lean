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

@[category research open, AMS 20]
theorem gnu_surjective : Function.Surjective gnu := by
  sorry


end GrpOfOrder
