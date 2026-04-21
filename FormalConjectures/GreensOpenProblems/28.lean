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
- [Mathoverflow/339137](https://mathoverflow.net/questions/339137/why-do-polynomials-with-coefficients-0-1-like-to-have-only-factors-with-0-1) asked by user [Sil](https://mathoverflow.net/users/136794/sil)
- [MathStackexchange/3325163](https://math.stackexchange.com/questions/3325163/) asked by user [Emmanuel Amiot](https://math.stackexchange.com/users/403309/emmanuel-amiot)
-/

namespace Green28

/-- True if a PMF on $\mathbb{Z}$ is uniformly distributed on its support. -/
def IsUniformOnSupport (X : PMF ℤ) : Prop :=
  ∃ (s : Finset ℤ) (hs : s.Nonempty), X = PMF.uniformOfFinset s hs

/--
The discrete convolution of two PMFs on $\mathbb{Z}$, representing the distribution of the sum of
two independent random variables.
-/
noncomputable def indepSum (X Y : PMF ℤ) : PMF ℤ := do
  let x ← X
  let y ← Y
  PMF.pure (x + y)

/--
Suppose that $X, Y$ are two finitely-supported independent random variables taking integer values,
and such that $X + Y$ is uniformly distributed on its range. Are $X$ and $Y$ themselves uniformly
distributed on their ranges?
-/
@[category research open, AMS 60]
theorem green_28 : answer(sorry) ↔
  ∀ (X Y : PMF ℤ), -- marginals, independence is built into indepSum
    X.support.Finite ∧ Y.support.Finite ∧ IsUniformOnSupport (indepSum X Y) →
      IsUniformOnSupport X ∧ IsUniformOnSupport Y := by
  sorry

end Green28
