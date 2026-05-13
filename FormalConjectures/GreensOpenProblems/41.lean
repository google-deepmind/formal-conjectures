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

open Complex Set Pointwise

/--
The pyjama set is the set of points in the complex plane whose real part is within $\varepsilon$ of
an integer.
-/
def pyjamaSet (ε : ℝ) : Set ℂ :=
  { z | ∃ k : ℤ, |z.re - (k : ℝ)| ≤ ε }

/-- The set of valid numbers of rotated copies of the pyjama set of width ε that cover the plane. -/
def coveringCopies (ε : ℝ) : Set ℕ :=
  { n : ℕ | ∃ (Θ : Finset ℝ), Θ.card = n ∧
    (⋃ θ ∈ Θ, exp (θ * I) • pyjamaSet ε) = univ }

/-- The minimal number of rotated copies of the pyjama set of width ε needed to cover the plane. -/
noncomputable def minCopies (ε : ℝ) : ℕ :=
  sInf (coveringCopies ε)

/--
[Ma15] proved that for any $\varepsilon > 0$, finitely many rotations of the pyjama set of width
$\varepsilon$ cover the plane. This implies that the set we are taking the infimum over in `minCopies`
is non-empty.
-/
@[category research solved, AMS 51 52]
theorem minCopies_set_nonempty (ε : ℝ) (hε : 0 < ε) :
    (coveringCopies ε).Nonempty := by
  sorry

/--
How many rotated (about the origin) copies of the 'pyjama set'
$\\{(x, y) \in \mathbb{R}^2 : \text{dist}(x, \mathbb{Z}) \leq \varepsilon\\}$ are needed to cover
$\mathbb{R}^2$?

In particular, can one find a better bound than the best-known bound from [KrLe25]?
-/
@[category research open, AMS 51 52]
theorem green_41 :
    ∃ C : ℝ, C > 0 ∧ ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀,
      let ans := (answer(sorry) : ℝ)
      (minCopies ε : ℝ) ≤ ans ∧ ans < Real.exp (Real.exp (Real.exp (ε ^ (-C)))) := by
  sorry

/--
Is there a better bound than the best-known bound from [KrLe25]?
This is an existential version of the main problem that does not require providing the bound explicitly.
-/
@[category research open, AMS 51 52]
theorem green_41.variants.exists_better_bound : answer(sorry) ↔
    ∃ C : ℝ, C > 0 ∧ ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀,
      ∃ ans : ℝ, (minCopies ε : ℝ) ≤ ans ∧ ans < Real.exp (Real.exp (Real.exp (ε ^ (-C)))) := by
  sorry

/-- Is $\varepsilon^{-C}$ rotations enough? -/
@[category research open, AMS 51 52]
theorem green_41.variants.polynomial_bound : answer(sorry) ↔
    ∃ C : ℝ, ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀, (minCopies ε : ℝ) ≤ ε ^ (-C) := by
  sorry

/--
[KrLe25] have established the first quantitative bound, showing via an analysis of [Ma15]'s method
that $\exp\exp\exp(\varepsilon^{-C})$ rotations suffice.
-/
@[category research solved, AMS 51 52]
theorem green_41.variants.kravitz_leng :
    ∃ C : ℝ, ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀, (minCopies ε : ℝ) ≤ Real.exp (Real.exp (Real.exp (ε ^ (-C)))) := by
  sorry

end Green41
