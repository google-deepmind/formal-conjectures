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
# Erdős Problem 990

*Reference:* [erdosproblems.com/990](https://www.erdosproblems.com/990)

Can the Erdős–Turán bound on the distribution of polynomial root arguments be improved by
replacing the degree with the number of non-zero coefficients?

[ErTu50] Erdős, P. and Turán, P., *On the distribution of roots of polynomials*, Annals of
Mathematics (1950).

[Er64b] Erdős, P., *On some problems relating to the distribution of roots of polynomials* (1964).
-/

open Polynomial Complex Real Finset

open scoped BigOperators

namespace Erdos990

/-- The argument of a complex number normalized to $[0, 2\pi)$.
Returns $0$ for $z = 0$. -/
noncomputable def Complex.arg2pi (z : ℂ) : ℝ :=
  if Complex.arg z < 0 then Complex.arg z + 2 * Real.pi else Complex.arg z

/-- The number of roots (counted with multiplicity) of a polynomial whose
argument lies in the interval $[\alpha, \beta]$. -/
noncomputable def rootArgCount (f : Polynomial ℂ) (α β : ℝ) : ℕ :=
  (f.roots.map Complex.arg2pi).countP (fun θ => decide (α ≤ θ ∧ θ ≤ β))

/-- The Erdős–Turán measure
$M(f) = \frac{|a_0| + \cdots + |a_d|}{\sqrt{|a_0| \cdot |a_d|}}$. -/
noncomputable def erdosTuranMeasure (f : Polynomial ℂ) : ℝ :=
  (∑ i ∈ Finset.range (f.natDegree + 1), ‖f.coeff i‖) /
    Real.sqrt (‖f.coeff 0‖ * ‖f.leadingCoeff‖)

/--
Erdős Problem 990 [Er64b]:

Let $f = a_0 + \cdots + a_d x^d \in \mathbb{C}[x]$ be a polynomial with roots
$z_1, \ldots, z_d$ with corresponding arguments $\theta_1, \ldots, \theta_d \in [0, 2\pi)$.
Is it true that for all intervals $[\alpha, \beta] \subseteq [0, 2\pi)$,
$$
\left|\#\{\theta_i \in [\alpha, \beta]\} - \frac{\beta - \alpha}{2\pi} \cdot d\right|
  \leq C \cdot \sqrt{n \cdot \log M}
$$
where $C$ is an absolute constant, $n$ is the number of non-zero coefficients of $f$, and
$M = \frac{|a_0| + \cdots + |a_d|}{\sqrt{|a_0| \cdot |a_d|}}$?

Erdős and Turán [ErTu50] proved such an upper bound with $n$ replaced by $d$ (the degree).
-/
@[category research open, AMS 12 30]
theorem erdos_990 : answer(sorry) ↔
    ∃ C : ℝ, C > 0 ∧
    ∀ (f : Polynomial ℂ),
      f.natDegree ≥ 1 →
      f.coeff 0 ≠ 0 →
      ∀ (α β : ℝ), 0 ≤ α → α ≤ β → β ≤ 2 * Real.pi →
        |(rootArgCount f α β : ℝ) - (β - α) / (2 * Real.pi) * ↑f.natDegree| ≤
          C * Real.sqrt (↑f.support.card * Real.log (erdosTuranMeasure f)) := by
  sorry

end Erdos990
