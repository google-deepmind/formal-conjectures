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
module

public import FormalConjecturesUtil

/-!
# Ben Green's Open Problem 46

What is the largest $y$ for which one may cover the interval $[y]$ by residue classes $a_p \pmod{p}$, one for each prime $p \leq x$?

*References:*
- [Gr24] [Ben Green's Open Problem 46](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.46)
- [FGK18] Ford, K., Green, B., Konyagin, S., Maynard, J., & Tao, T. (2018). Long gaps between primes.
  Journal of the American Mathematical Society, 31(1), 65-105.
- [Iw78] Iwaniec, Henryk. "On the problem of Jacobsthal." Demonstratio Mathematica 11.1 (1978): 225-232.
- [OAI26a] OpenAI, *A quadratic bound for Jacobsthal's function*. OpenAI Math Release preprint
  (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf
- [Ra38] Rankin, R. A., *The difference between consecutive prime numbers*. J. London Math. Soc.
  (1938), 242--247.

This is the same problem as Erdős Problem 687.
-/

@[expose] public section

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

/-- Best-known lower bound [FGK18], improving on [Ra38]. -/
noncomputable def bestLower (x : ℕ) : ℝ :=
  (x : ℝ) * Real.log (x : ℝ) * Real.log (Real.log (Real.log (x : ℝ))) / Real.log (Real.log (x : ℝ))

/-- Best-known upper bound [Iw78]. -/
noncomputable def bestUpper (x : ℕ) : ℝ := (x : ℝ) ^ 2

def green_46.improve_lower.answer : ℕ → ℝ := sorry

/-- We conjecture that the best-known lower bound can be improved. -/
@[category research open, question value, AMS 11]
theorem green_46.improve_lower :
    (bestLower =o[atTop] green_46.improve_lower.answer) ∧ (green_46.improve_lower.answer ≪ maxY)
      := by
  sorry

noncomputable def green_46.improve_upper.answer : ℕ → ℝ :=
  fun x : ℕ ↦ ((x : ℝ) + 1) ^ 2 / (Real.log (Real.log (3 * ((x : ℝ) + 1)))) ^ 2

/-- We conjecture that the best-known upper bound can be improved.

Yes. OpenAI [OAI26a] proved $h(k) \ll k^2 / (\log\log 3k)^2$ for Jacobsthal's function $h$
(Erdős Problem 970). By the Chinese remainder theorem $\mathrm{maxY}(x) < h(\pi(x))$, which gives
$\mathrm{maxY}(x) \ll (x+1)^2 / (\log\log 3(x+1))^2 = o(x^2)$. Whether $y \ll x^{1+o(1)}$ remains
open, see `green_46.improve_upper_conjectured`. -/
@[category research solved, question value, AMS 11, formal_proof using lean4 at
  "https://github.com/30k30/scholia/blob/b072c89c3edac06521868e32cc15b2bc91bd8533/erdos-687/glue/JacobsthalTo687.lean#L319"]
theorem green_46.improve_upper :
    (green_46.improve_upper.answer =o[atTop] bestUpper) ∧ (maxY ≪ green_46.improve_upper.answer)
      := by
  sorry

/-- It seems very likely that we must have $y \ll x^{1+o(1)}$ [Gr24]. -/
@[category research open, AMS 11]
theorem green_46.improve_upper_conjectured :
    ∃ o : ℕ → ℝ, (o =o[atTop] fun _ : ℕ ↦ (1 : ℝ)) ∧
      maxY ≪ fun x ↦ (x : ℝ) ^ (1 + o x) := by
  sorry

/-- Best known lower bound: $y \gg x \frac{\log x \log \log \log x}{\log \log x}$ [FGK18]. -/
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
