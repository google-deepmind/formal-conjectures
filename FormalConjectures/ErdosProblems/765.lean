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
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Erdős Problem 765

*Reference:* [erdosproblems.com/765](https://www.erdosproblems.com/765)

Give an asymptotic formula for $\mathrm{ex}(n; C_4)$.

Erdős and Klein proved $\mathrm{ex}(n; C_4) \asymp n^{3/2}$. Reiman proved
$\frac{1}{2\sqrt{2}} \leq \lim \frac{\mathrm{ex}(n; C_4)}{n^{3/2}} \leq \frac{1}{2}$.
Erdős–Rényi and independently Brown showed that for $n = q^2 + q + 1$ with $q$ a
prime power, $\mathrm{ex}(n; C_4) \geq \frac{q(q+1)^2}{2}$, which together with Reiman's
upper bound gives $\mathrm{ex}(n; C_4) \sim \frac{1}{2} n^{3/2}$.

Füredi [Fu83] proved exact values for $q > 13$:
$\mathrm{ex}(n; C_4) = \frac{1}{2} q(q+1)^2$ when $n = q^2 + q + 1$ and $q$ is a prime power.

[Er93] Erdős, P., *On some of my favourite theorems*. Combinatorics, Paul Erdős is eighty,
Vol. 2 (Keszthely, 1993), 97–132.

[Fu83] Füredi, Z., *Graphs without quadrilaterals*. J. Combin. Theory Ser. B (1983), 187–190.

[MaYa23] Ma, J. and Yang, T., *On the extremal number of subdivisions*. Combinatorica 43
(2023), 1019–1027.
-/

open SimpleGraph

namespace Erdos765

/--
Erdős Problem 765 (SOLVED):

The asymptotic formula for $\mathrm{ex}(n; C_4)$ is
$\mathrm{ex}(n; C_4) \sim \frac{1}{2} n^{3/2}$.

Formally: for every $\varepsilon > 0$, there exists $N_0$ such that for all $n \geq N_0$,
$$\left|\frac{\mathrm{ex}(n; C_4)}{n^{3/2}} - \frac{1}{2}\right| < \varepsilon.$$
-/
@[category research solved, AMS 5]
theorem erdos_765 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      |(↑(extremalNumber n (cycleGraph 4)) / (n : ℝ) ^ ((3 : ℝ) / 2) - 1 / 2)| < ε := by
  sorry

/--
Erdős's refined conjecture from [Er93] (still open):

$\mathrm{ex}(n; C_4) = \frac{n^{3/2}}{2} + O(n)$.

Formally: there exists a constant $C > 0$ such that for all $n \geq 1$,
$$\left|\mathrm{ex}(n; C_4) - \frac{n^{3/2}}{2}\right| \leq C \cdot n.$$

His even stronger conjecture $\mathrm{ex}(n; C_4) = \frac{n^{3/2}}{2} + \frac{n}{4} +
O(n^{1/2})$ was disproved by Ma–Yang [MaYa23].
-/
@[category research open, AMS 5]
theorem erdos_765.variants.refined :
    ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      |(↑(extremalNumber n (cycleGraph 4)) - (n : ℝ) ^ ((3 : ℝ) / 2) / 2)| ≤
        C * (n : ℝ) := by
  sorry

/--
Erdős's stronger conjecture (DISPROVED by Ma–Yang [MaYa23]):

$\mathrm{ex}(n; C_4) = \frac{n^{3/2}}{2} + \frac{n}{4} + O(n^{1/2})$.

Formally: there exists a constant $C > 0$ such that for all $n \geq 1$,
$$\left|\mathrm{ex}(n; C_4) - \frac{n^{3/2}}{2} - \frac{n}{4}\right| \leq C \cdot n^{1/2}.$$

This is a refinement of the O(n) variant; it pins down the second-order term as $n/4$.
Ma and Yang showed this is false.
-/
@[category research solved, AMS 5]
theorem erdos_765.variants.strong_conjecture :
    ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      |(↑(extremalNumber n (cycleGraph 4)) - (n : ℝ) ^ ((3 : ℝ) / 2) / 2 -
        (n : ℝ) / 4)| ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  sorry

end Erdos765
