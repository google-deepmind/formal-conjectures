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
# Ben Green's Open Problem 3

*Reference:* [Ben Green's Open Problem 3](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.3 Problem 3)
-/

open Set MeasureTheory

namespace Green3

/-- Suppose that $A \subset [0,1]$ is open and has measure greater than $\frac{1}{3}$. Is there a solution to $xy = z$ with $x, y, z \in A$? -/
@[category research open, AMS 11]
theorem green_3 :
    answer(sorry) ↔ ∀ A : Set ℝ,
      IsOpen A →
      A ⊆ Icc 0 1 →
      volume A > 1/3 →
      ∃ x y z, x ∈ A ∧ y ∈ A ∧ z ∈ A ∧ x * y = z := by
sorry

end Green3


