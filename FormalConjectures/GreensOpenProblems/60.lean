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

open scoped Pointwise

/-!
# Ben Green's Open Problem 60

*Reference:* [Ben Green's Open Problem 60](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.8 Problem 60)
-/

namespace Green60

/--
Is there an absolute constant $c > 0$ such that, whenever $A ⊆ \mathbb{N}$ is a set of squares
with $|A| ≥ 2$, the sumset $A + A$ satisfies $|A + A| ≥ |A|^{1 + c}$?
-/
@[category research open, AMS 11]
theorem green_60 :
    answer(sorry) ↔ ∃ c > (0 : ℝ),
      ∀ (A : Finset ℕ),
        (∀ a ∈ A, IsSquare a) →
        2 ≤ A.card →
          ((A + A).card : ℝ) ≥ Real.rpow (A.card : ℝ) (1 + c) := by
  sorry

end Green60
