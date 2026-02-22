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
# Green's Open Problem 28

References:
- [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.28)
-/

namespace Green28

open PMF

/-- A PMF on $\mathbb{Z}$ is uniformly distributed on its range if all non-zero probabilities are equal. -/
def IsUniformOnSupport (X : PMF ℤ) : Prop :=
  ∃ c : NNReal, ∀ x ∈ X.support, X x = c

/-- The sum of two independent PMFs on $\mathbb{Z}$. -/
noncomputable def indepSum (X Y : PMF ℤ) : PMF ℤ :=
  X.bind (fun x ↦ Y.map (fun y ↦ x + y))

/--
Suppose that $X, Y$ are two finitely-supported independent random variables taking integer values,
and such that $X + Y$ is uniformly distributed on its range. Are $X$ and $Y$ themselves uniformly
distributed on their ranges?
-/
@[category research open, AMS 60]
theorem green_28 : answer(sorry) ↔
  ∀ (X Y : PMF ℤ),
    X.support.Finite →
    Y.support.Finite →
    IsUniformOnSupport (indepSum X Y) →
    IsUniformOnSupport X ∧ IsUniformOnSupport Y := by
  sorry

end Green28
