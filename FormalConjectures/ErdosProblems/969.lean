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
# Erdős Problem 969

*Reference:* [erdosproblems.com/969](https://www.erdosproblems.com/969)

Let $Q(x)$ count the number of squarefree integers in $[1, x]$. The asymptotic is
$Q(x) = (6/\pi^2)x + E(x)$. It is elementary that $E(x) \ll x^{1/2}$, and the prime
number theorem gives $o(x^{1/2})$. Evelyn and Linfoot [EvLi31] proved
$E(x) = \Omega(x^{1/4})$, and this is likely the true order of magnitude.
The best unconditional bound is due to Walfisz [Wa63].
Assuming the Riemann Hypothesis, Liu [Li16] proved
$E(x) = O(x^{11/35 + o(1)})$, but the true order of magnitude remains unknown even
under RH. Note that the sharp bound $E(x) = O(x^{1/4})$ (without $\varepsilon$)
would imply the Riemann Hypothesis; the conjecture formalized here,
$E(x) = O(x^{1/4 + \varepsilon})$ for all $\varepsilon > 0$, is strictly weaker and
does not imply RH.

## References

* [EvLi31] Evelyn, C. J. A., Linfoot, E. H., _On a problem in the additive theory of
  numbers_. Ann. of Math. (2) (1931), 261–270.
* [Wa63] Walfisz, A., _Weylsche Exponentialsummen in der neueren Zahlentheorie_ (1963),
  p. 231.
* [Li16] Liu, H.-Q., _On the distribution of squarefree numbers_. J. Number Theory
  (2016), 202–222.

## See also

* [OEIS A013928](https://oeis.org/A013928) — Number of squarefree numbers up to $n$.
-/

open Finset Real

namespace Erdos969

/-- The number of squarefree positive integers in $[1, x]$. -/
def squarefreeCount (x : ℕ) : ℕ :=
  ((Icc 1 x).filter Squarefree).card

/-- The error term $E(x) = Q(x) - (6/\pi^2)x$ in the squarefree counting asymptotic. -/
noncomputable def squarefreeError (x : ℕ) : ℝ :=
  (squarefreeCount x : ℝ) - (6 / Real.pi ^ 2) * (x : ℝ)

/--
Erdős Problem 969: The error term $E(x)$ in the squarefree counting function
$Q(x) = (6/\pi^2)x + E(x)$ satisfies $E(x) = O(x^{1/4 + \varepsilon})$ for every
$\varepsilon > 0$. Combined with the known lower bound $E(x) = \Omega(x^{1/4})$
of Evelyn and Linfoot [EvLi31], this would establish that $x^{1/4}$ is the true order of
magnitude of $E(x)$.

Note: this is strictly weaker than the sharp bound $E(x) = O(x^{1/4})$, which would
imply the Riemann Hypothesis. The $\varepsilon$-relaxed form formalized here does not
imply RH.

Formalized as: for every $\varepsilon > 0$, there exists $C > 0$ and $x_0$ such that
for all $x \geq x_0$, $|E(x)| \leq C \cdot x^{1/4 + \varepsilon}$.
-/
@[category research open, AMS 11]
theorem erdos_969 (ε : ℝ) (hε : ε > 0) :
    ∃ C : ℝ, C > 0 ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x ≥ x₀ →
      |squarefreeError x| ≤ C * (x : ℝ) ^ ((1 : ℝ) / 4 + ε) := by
  sorry

/--
Evelyn-Linfoot lower bound [EvLi31]: The error term $E(x)$ in the squarefree counting
function satisfies $E(x) = \Omega(x^{1/4})$, i.e., $|E(x)|$ is infinitely often at
least as large as a constant times $x^{1/4}$. This is the complementary lower bound to
the conjectured upper bound in `erdos_969`.
-/
@[category research solved, AMS 11]
theorem erdos_969_lower :
    ∃ C : ℝ, C > 0 ∧ ∀ x₀ : ℕ, ∃ x : ℕ, x ≥ x₀ ∧
      |squarefreeError x| ≥ C * (x : ℝ) ^ ((1 : ℝ) / 4) := by
  sorry

end Erdos969
