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

import FormalConjecturesUtil

/-!
# Dirichlet divisor problem

Let $d(n)$ be the number of divisors of $n$ and $D(x) = \sum_{n \le x} d(n)$ the divisor
summatory function. Dirichlet's hyperbola method gives
$$D(x) = x \log x + (2\gamma - 1) x + \Delta(x), \qquad \Delta(x) = O(x^{1/2}),$$
where $\gamma$ is the Euler–Mascheroni constant. The **Dirichlet divisor problem** asks for the
infimum $\theta$ of exponents with $\Delta(x) = O(x^{\theta})$. It is conjectured that
$\theta = 1/4$, i.e. $\Delta(x) = O(x^{1/4 + \varepsilon})$ for every $\varepsilon > 0$. Hardy
showed $\theta \ge 1/4$, so the conjecture would be sharp; the best known upper bound is due to
Huxley ($\theta \le 131/416 \approx 0.3149$), and the problem is open.

*References:*
- [Wikipedia: Divisor summatory function](https://en.wikipedia.org/wiki/Divisor_summatory_function)
- [Wikipedia: Dirichlet divisor problem](https://en.wikipedia.org/wiki/Divisor_summatory_function#Dirichlet's_divisor_problem)
- [Di49] P. G. L. Dirichlet, *Über die Bestimmung der mittleren Werthe in der Zahlentheorie*,
  Abhandl. Königl. Preuss. Akad. Wiss. (1849), 69-83.
- [Ha16] G. H. Hardy, *On Dirichlet's divisor problem*, Proc. London Math. Soc. (1916), 1-25.
- [Hu03] M. N. Huxley, *Exponential sums and lattice points III*, Proc. London Math. Soc.
  (2003), 591-609.
-/

open Filter Asymptotics Real

namespace DirichletDivisorProblem

/-- The divisor summatory function $D(x) = \sum_{n \le x} d(n)$, where $d(n)$ is the number of
divisors of $n$. -/
noncomputable def D (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)

/-- The error term $\Delta(x) = D(x) - x \log x - (2\gamma - 1) x$ in the divisor summatory
asymptotic, where $\gamma$ is the Euler–Mascheroni constant. -/
noncomputable def Δ (x : ℝ) : ℝ :=
  D x - x * Real.log x - (2 * eulerMascheroniConstant - 1) * x

/-- $D(1) = d(1) = 1$. -/
@[category test, AMS 11]
theorem D_one : D 1 = 1 := by
  simp only [D, Nat.floor_one, Finset.Icc_self, Finset.sum_singleton, Nat.divisors_one,
    Finset.card_singleton, Nat.cast_one]

/-- Dirichlet's bound [Di49]: $\Delta(x) = O(x^{1/2})$. -/
@[category research solved, AMS 11]
theorem divisor_error_dirichlet :
    Δ =O[atTop] fun x => Real.sqrt x := by
  sorry

/--
The Dirichlet divisor problem: is it true that $\Delta(x) = O(x^{1/4 + \varepsilon})$ for every
$\varepsilon > 0$? (Equivalently, is the infimum of admissible exponents equal to $1/4$?)
-/
@[category research open, AMS 11]
theorem dirichlet_divisor_problem :
    ∀ ε > (0 : ℝ), Δ =O[atTop] fun x => x ^ ((1 : ℝ) / 4 + ε) := by
  sorry

/--
Hardy's lower bound [Ha16]: $\Delta(x)$ is not $o(x^{1/4})$, so the exponent $1/4$ in the
Dirichlet divisor problem cannot be improved.
-/
@[category research solved, AMS 11]
theorem divisor_error_hardy :
    ¬ (Δ =o[atTop] fun x => x ^ ((1 : ℝ) / 4)) := by
  sorry

end DirichletDivisorProblem
