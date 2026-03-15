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
# Erdős Problem 1039

*Reference:* [erdosproblems.com/1039](https://www.erdosproblems.com/1039)

Let $f(z) = \prod_{i=1}^{n} (z - z_i) \in \mathbb{C}[z]$ with $|z_i| \le 1$ for all $i$. Let
$\rho(f)$ be the radius of the largest disc contained in $\{z : |f(z)| < 1\}$.

Is it true that $\rho(f) \gg 1/n$?

A problem of Erdős, Herzog, and Piranian [EHP58, p.134].

Known results:
- $f(z) = z^n - 1$ gives $\rho(f) \le \pi/(2n)$
- Pommerenke [Po61] proved $\rho(f) \ge 1/(2en^2)$
- Krishnapur, Lundberg, Ramachandran [KLR25] proved $\rho(f) \gg 1/(n\sqrt{\log n})$

[EHP58] Erdős, P., Herzog, F., and Piranian, G., _Metric properties of polynomials_. J. Analyse
Math. 6 (1958), 125-148.

[Po61] Pommerenke, Ch., _On metric properties of complex polynomials_. Michigan Math. J. 8 (1961),
97–115.

[KLR25] Krishnapur, M., Lundberg, E., and Ramachandran, K., _On the area of polynomial
lemniscates_. arXiv:2503.18270 (2025).
-/

open Polynomial Classical

namespace Erdos1039

/-- The sublevel radius $\rho(f)$: the supremum of radii $r > 0$ such that some open
disc of radius $r$ is contained in $\{z : \|f(z)\| < 1\}$. -/
noncomputable def sublevelRadius (f : Polynomial ℂ) : ℝ :=
  sSup {r : ℝ | r > 0 ∧ ∃ c : ℂ, Metric.ball c r ⊆ {z : ℂ | ‖f.eval z‖ < 1}}

/--
Erdős Problem 1039 [EHP58, p.134]:

For monic complex polynomials of degree $n \ge 1$ with all roots in the closed
unit disk, the sublevel radius $\rho(f)$ is at least $C/n$ for some absolute
constant $C > 0$.
-/
@[category research open, AMS 30]
theorem erdos_1039 : answer(sorry) ↔
    ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (f : Polynomial ℂ),
      1 ≤ n → f.Monic → f.natDegree = n →
      (∀ z ∈ f.roots, ‖z‖ ≤ 1) →
      sublevelRadius f ≥ C / (n : ℝ) := by
  sorry

end Erdos1039
