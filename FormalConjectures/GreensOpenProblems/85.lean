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
# Green's Open Problem 85

*Carbery’s rectangle problem*

References:
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.85)
- [CCW99] Carbery, Anthony, Michael Christ, and James Wright. "Multidimensional van der Corput and sublevel set estimates." Journal of the American Mathematical Society 12.4 (1999): 981-1015 Section 6.
- [Ke00] Keleti, Tamás. "Density and covering properties of intervals of ℝn." Mathematika 47.1-2 (2000): 229-242.
- [KKM02] Katz, Nets Hawk, Elliot Krop, and Mauro Maggioni. "Remarks on the box problem." Mathematical Research Letters 9.4 (2002): 515-520.
- [Mu02] Mubayi, Dhruv. "Some exact results and new asymptotics for hypergraph Turán numbers." Combinatorics, Probability and Computing 11.3 (2002): 299-309 Conjecture 1.4.
- [CPZ20] Conlon, David, Cosmin Pohoata, and Dmitriy Zakharov. "Random multilinear maps and the Erd\H {o} s box problem." arXiv preprint arXiv:2011.09024 (2020).
-/

open Filter MeasureTheory Set

namespace Green85

/--
Suppose that $A$ is an open subset of $[0, 1]^2$ with measure $\alpha$. Are there four points in
$A$ determining an axis-parallel rectangle with area $\gt c \alpha^2$?
-/
@[category research open, AMS 28 52]
theorem green_85 :
  answer(sorry) ↔ ∃ c > 0, ∀ A : Set (ℝ × ℝ),
    IsOpen A →
    A ⊆ Icc 0 1 ×ˢ Icc 0 1 →
    A.Nonempty →
    let α := (volume A).toReal
    ∃ x₁ x₂ y₁ y₂,
      {(x₁, y₁), (x₂, y₁), (x₂, y₂), (x₁, y₂)} ⊆ A ∧
      c * α ^ 2 ≤ |x₁ - x₂| * |y₁ - y₂| := by
  sorry

/--
From [Gr24] "It is quite easy to show using Cauchy-Schwarz that there must be such a rectangle with
area $\gg \alpha^2 (\log 1/\alpha)^{-1}$."
-/
@[category research solved, AMS 28 52]
theorem green_85_loose :
    ∃ c > 0, ∀ A : Set (ℝ × ℝ),
    IsOpen A →
    A ⊆ Icc 0 1 ×ˢ Icc 0 1 →
    A.Nonempty →
    let α := (volume A).toReal
    ∃ x₁ x₂ y₁ y₂,
      {(x₁, y₁), (x₂, y₁), (x₂, y₂), (x₁, y₂)} ⊆ A ∧
      α ^ 2 * (Real.log (1/α))⁻¹ ≤ |x₁ - x₂| * |y₁ - y₂| := by
  sorry

end Green85
