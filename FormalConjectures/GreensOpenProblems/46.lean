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
# Ben Green's Open Problem 46

What is the largest $y$ for which one may cover the interval $[y]$ by residue classes $a_p \pmod{p}$, one for each prime $p \leq x$?

*References:*
- [Gr24] [Ben Green's Open Problem 46](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.46)
- [FGK18] Ford, K., Green, B., Konyagin, S., Maynard, J., & Tao, T. (2018). Long gaps between primes.
  Journal of the American Mathematical Society, 31(1), 65-105.
- [Iw78] Iwaniec, Henryk. "On the problem of Jacobsthal." Demonstratio Mathematica 11.1 (1978): 225-232.
-/

namespace Green46

open Filter
open scoped Asymptotics

/-- Given $x$ and $y$, can we cover the interval $[1, y]$ by residue classes $a_p \pmod p$
for each prime $p \le x$? -/
def IsCoveredByResidues (x y : ℕ) : Prop :=
  ∃ a : ℕ → ℕ, ∀ m ∈ Finset.Icc 1 y, ∃ p ≤ x, p.Prime ∧ m ≡ a p [MOD p]

/-- The maximum $y$ for a given $x$, cast to a real number for asymptotics. -/
noncomputable def maxY (x : ℕ) : ℝ :=
  ((sSup { y | IsCoveredByResidues x y } : ℕ) : ℝ)

/-- Best-known lower bound [Ra38]. -/
noncomputable def bestLower (x : ℕ) : ℝ :=
  (x : ℝ) * Real.log (x : ℝ) * Real.log (Real.log (Real.log (x : ℝ))) / Real.log (Real.log (x : ℝ))

/-- Best-known upper bound [Iw78]. -/
noncomputable def bestUpper (x : ℕ) : ℝ := (x : ℝ) ^ 2

/-- We conjecture that the best-known lower bound can be improved. -/
@[category research open, AMS 11]
theorem green_46.improve_lower :
    let ans := (answer(sorry) : ℕ → ℝ)
    (bestLower =o[atTop] ans) ∧ (ans ≪ maxY) := by
  sorry

/-- We conjecture that the best-known upper bound can be improved. -/
@[category research open, AMS 11]
theorem green_46.improve_upper :
    let ans := (answer(sorry) : ℕ → ℝ)
    (ans =o[atTop] bestUpper) ∧ (maxY ≪ ans) := by
  sorry

/-- It seems very likely that we must have $y \ll x^{1+o(1)}$ [Gr24]. -/
@[category research open, AMS 11]
theorem green_46.improve_upper_conjectured :
    ∃ o : ℕ → ℝ, (o =o[atTop] fun _ : ℕ ↦ (1 : ℝ)) ∧
      maxY ≪ fun x ↦ (x : ℝ) ^ (1 + o x) := by
  sorry

/-- Best known lower bound: $y \gg x \frac{\log x \log \log \log x}{\log \log x}$ [Ra38]. -/
@[category research solved, AMS 11]
theorem green_46.variants.lower :
    bestLower ≪ maxY := by
  sorry

/-- Best known upper bound: $y \ll x^2$ [Iw78]. -/
@[category research solved, AMS 11]
theorem green_46.variants.upper :
    maxY ≪ bestUpper := by
  sorry

-- TODO(jeangud) Add similar problem mentioned in [Gr24, Problem 46]

end Green46
