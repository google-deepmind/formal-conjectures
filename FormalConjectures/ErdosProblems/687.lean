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
# Erdős Problem 687

Let $Y(x)$ be the maximal $y$ such that one can choose one residue class $a_p \pmod{p}$
for every prime $p \le x$ so that every integer in $\{1, \ldots, y\}$ is covered by at
least one of these classes. Is it true that $Y(x) = o(x^2)$? Or even
$Y(x) \ll x^{1+o(1)}$?

Iwaniec [Iw78] proved the upper bound $Y(x) \ll x^2$. Ford, Green, Konyagin,
Maynard, and Tao [FGKMT18] proved the lower bound
$Y(x) \gg x \cdot (\log x)(\log \log \log x)/(\log \log x)$.
Maier and Pomerance conjectured $Y(x) \ll x(\log x)^{2+o(1)}$.

[Er80] Erdős, P., *A survey of problems in combinatorial number theory*.
Annals of Discrete Mathematics (1980), 89–115.

[Iw78] Iwaniec, H., *On the problem of Jacobsthal*.
Demonstratio Mathematica (1978), 225–231.

[FGKMT18] Ford, K., Green, B., Konyagin, S., Maynard, J., Tao, T.,
*Long gaps between primes*. Journal of the American Mathematical Society (2018), 65–105.

[Ra38] Rankin, R. A., *The Difference between Consecutive Prime Numbers*.
Journal of the London Mathematical Society (1938), 242–247.

OEIS: A048670, A058989.

See also problems #4, #688, #689, #970.

*Reference:* [erdosproblems.com/687](https://www.erdosproblems.com/687)
-/

namespace Erdos687

/--
A choice of residue classes for primes $p \le x$ covers $[1, y]$ if every
integer $n \in \{1, \ldots, y\}$ is congruent to $a(p) \pmod{p}$ for some prime $p \le x$.
This captures a covering system related to the Jacobsthal function.
-/
def PrimeCovering (x y : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ y → ∃ p : ℕ, p.Prime ∧ p ≤ x ∧ n % p = a p % p

/--
Erdős Problem 687 (weak form): $Y(x) = o(x^2)$.
Let $Y(x)$ be the maximal $y$ such that there exists a choice of congruence
classes $a_p$ for all primes $p \le x$ such that every integer in $[1, y]$ is
congruent to at least one of the $a_p \pmod{p}$. Then $Y(x) = o(x^2)$.
-/
@[category research open, AMS 11]
theorem erdos_687 :
    answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 → ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
    ∀ (a : ℕ → ℕ) (y : ℕ), PrimeCovering x y a →
    (y : ℝ) < ε * (x : ℝ) ^ 2 := by
  sorry

/--
Erdős Problem 687 (strong form): $Y(x) \ll x^{1+o(1)}$.
For every $\varepsilon > 0$, for all sufficiently large $x$, any covering of $[1, y]$
by residue classes of primes $\le x$ satisfies $y \le x^{1+\varepsilon}$.
-/
@[category research open, AMS 11]
theorem erdos_687.variants.strong :
    answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 → ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
    ∀ (a : ℕ → ℕ) (y : ℕ), PrimeCovering x y a →
    (y : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) + ε) := by
  sorry

end Erdos687
