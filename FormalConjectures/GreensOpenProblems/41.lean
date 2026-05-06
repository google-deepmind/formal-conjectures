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
# Ben Green's Open Problem 41

*References*
- [Gr24] [Ben Green's Open Problem 41](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.41)
- [Ma15] Manners, Freddie. "A solution to the pyjama problem." Inventiones mathematicae 202.1 (2015): 239-270.
- [KrLe25] Kravitz, Noah, and James Leng. "Quantitative pyjama." arXiv preprint arXiv:2510.17744 (2025).

-/

namespace Green41

open Set

/-- The pyjama set is the set of points in the plane whose x-coordinate is within ε of an integer. -/
def pyjamaSet (ε : ℝ) : Set (ℝ × ℝ) :=
  { p | ∃ z : ℤ, |p.1 - (z : ℝ)| ≤ ε }

/-- A rotation about the origin by angle θ. -/
noncomputable def rotate (θ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 * Real.cos θ - p.2 * Real.sin θ, p.1 * Real.sin θ + p.2 * Real.cos θ)

/--
How many rotated (about the origin) copies of the 'pyjama set' $\\{(x, y) \in \mathbb{R}^2 : \text{dist}(x, \mathbb{Z}) \leq \varepsilon\\}$ are needed to cover $\mathbb{R}^2$?
-/
@[category research open, AMS 51 52]
theorem green_41 :
    ∀ ε > 0,
      let ans := (answer(sorry) : ℕ)
      IsLeast { n : ℕ | ∃ (Θ : Finset ℝ), Θ.card = n ∧ ∀ p : ℝ × ℝ, ∃ θ ∈ Θ, p ∈ rotate θ '' pyjamaSet ε } ans := by
  sorry

end Green41
