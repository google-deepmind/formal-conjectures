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
number theorem gives $o(x^{1/2})$. Evelyn and Linfoot proved $E(x) = \Omega(x^{1/4})$,
and this is likely the true order of magnitude. The Riemann Hypothesis would follow from
$E(x) = O(x^{1/4})$.
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
of Evelyn and Linfoot, this would establish that $x^{1/4}$ is the true order of
magnitude of $E(x)$.

Formalized as: for every $\varepsilon > 0$, there exists $C > 0$ and $x_0$ such that
for all $x \geq x_0$, $|E(x)| \leq C \cdot x^{1/4 + \varepsilon}$.
-/
@[category research open, AMS 11]
theorem erdos_969 (ε : ℝ) (hε : ε > 0) :
    ∃ C : ℝ, C > 0 ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x ≥ x₀ →
      |squarefreeError x| ≤ C * (x : ℝ) ^ ((1 : ℝ) / 4 + ε) := by
  sorry

end Erdos969
