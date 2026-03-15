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
# Erdős Problem 450

*Reference:* [erdosproblems.com/450](https://www.erdosproblems.com/450)

How large must $y = y(\varepsilon, n)$ be such that the number of integers in $(x, x+y)$ with a
divisor in $(n, 2n)$ is at most $\varepsilon \cdot y$?

The intended quantifier on $x$ is not entirely clear from the original source. We formalize
the "for all $x$" interpretation: there exists a constant $C > 0$ such that for all sufficiently
large $n$ and all $\varepsilon \geq C / f(n)$ (where
$f(n) = (\log n)^{\alpha} \cdot (\log \log n)^{3/2}$ and
$\alpha = 1 - (1 + \log \log 2)/\log 2 \approx 0.08607$ is the Ford constant), there exists $y$
such that for all $x$, the count of integers in $(x, x+y)$ with a divisor in $(n, 2n)$ is at most
$\varepsilon \cdot y$.

The hypothesis on $\varepsilon$ is necessary: Cambie observed (using Ford's results [Fo08]) that
the unconditioned "for all $x$" version fails when
$\varepsilon \cdot (\log n)^{\alpha} \cdot (\log \log n)^{3/2} \to \infty$. In particular, for
any fixed $\varepsilon > 0$ and all sufficiently large $n$, no such $y$ exists. The condition
$\varepsilon \geq C / f(n)$ restricts to the regime where $\varepsilon$ is comparable to the
natural density $\delta(n) \asymp 1/f(n)$ of integers with a divisor in $(n, 2n)$.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[Fo08] Ford, K., *The distribution of integers with a divisor in a given interval*. Ann. of Math.
(2) **168** (2008), 367–433.
-/

open Finset Classical

namespace Erdos450

/-- Count of integers in the open interval $(x, x + y)$ having at least one divisor
in the open interval $(n, 2n)$. -/
noncomputable def countWithDivisorInRange (x y n : ℕ) : ℕ :=
  ((Finset.Ioo x (x + y)).filter (fun m =>
    ∃ d ∈ Finset.Ioo n (2 * n), d ∣ m)).card

/-- The Ford constant $\alpha = 1 - \frac{1 + \log(\log 2)}{\log 2} \approx 0.08607$,
governing the density of integers with a divisor in a given interval. -/
noncomputable def fordAlpha : ℝ := 1 - (1 + Real.log (Real.log 2)) / Real.log 2

/--
Erdős Problem 450 [ErGr80, p.89]:

There exists a constant $C > 0$ such that for all sufficiently large $n$ and all
$\varepsilon \geq C / ((\log n)^{\alpha} \cdot (\log \log n)^{3/2})$, there exists $y$ such that
for all $x$, the number of integers in $(x, x + y)$ with a divisor in $(n, 2n)$ is at most
$\varepsilon \cdot y$.
-/
@[category research open, AMS 11]
theorem erdos_450 :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → ∀ ε : ℝ, 0 < ε →
      ε ≥ C / ((Real.log ↑n) ^ fordAlpha * (Real.log (Real.log ↑n)) ^ ((3 : ℝ) / 2)) →
      ∃ y : ℕ, 0 < y ∧ ∀ x : ℕ,
        (countWithDivisorInRange x y n : ℝ) ≤ ε * (y : ℝ) := by
  sorry

end Erdos450
