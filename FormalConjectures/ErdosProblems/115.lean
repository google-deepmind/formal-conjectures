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
# Erdős Problem 115

*Reference:* [erdosproblems.com/115](https://www.erdosproblems.com/115)

If the lemniscate $\{z : |p(z)| \leq 1\}$ of a degree-$n$ polynomial is connected, then
$|p'(z)| \leq (1/2 + o(1)) n^2$ on it. Proved by Eremenko and Lempert.

[Er61, Er90] Early formulations by Erdős.
[ErLe94] Eremenko, A. and Lempert, L., _An extremal problem for polynomials_.
  Proc. Amer. Math. Soc. 122 (1994), 191–193.
[Po59a] Pommerenke, Ch., _On the derivative of a polynomial_.
  Michigan Math. J. 6 (1959), 373–375.
-/

open Polynomial

namespace Erdos115

/-- The lemniscate of a complex polynomial $p$: the sublevel set
$\{z \in \mathbb{C} : |p(z)| \leq 1\}$. -/
def lemniscate (p : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ ≤ 1}

/--
Erdős Conjecture (Problem #115) [Er61, Er90], proved by Eremenko–Lempert [ErLe94]:

If $p(z)$ is a monic polynomial of degree $n$ such that $\{z \in \mathbb{C} : |p(z)| \leq 1\}$
is connected, then
$$\max \{ |p'(z)| : z \in \mathbb{C},\, |p(z)| \leq 1 \} \leq (1/2 + o(1))\, n^2.$$

That is, for every $\varepsilon > 0$ there exists $N$ such that for all $n \geq N$, every
monic polynomial $p$ of degree $n$ whose lemniscate is connected satisfies
$|p'(z)| \leq (1/2 + \varepsilon)\, n^2$ for all $z$ in the lemniscate.

Erdős originally conjectured the bound $n^2/2$ exactly (without the $o(1)$), but Szabados
observed that the stronger form fails. Pommerenke [Po59a] proved the weaker bound
$(e/2)\, n^2$. The monicness hypothesis is essential: without it, Chebyshev polynomials
$T_n$ provide a counterexample, since $|T_n'(1)| = n^2$ while $\{z : |T_n(z)| \leq 1\}$
is connected.
-/
@[category research solved, AMS 30]
theorem erdos_115 :
    ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
      IsConnected (lemniscate p) →
      ∀ z : ℂ, z ∈ lemniscate p →
        ‖(derivative p).eval z‖ ≤ (1 / 2 + ε) * (n : ℝ) ^ 2 := by
  sorry

end Erdos115
