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
# Erdős Problem 1045

*Reference:* [erdosproblems.com/1045](https://www.erdosproblems.com/1045)

Let $z_1, \ldots, z_n \in \mathbb{C}$ with $|z_i - z_j| \le 2$ for all $i, j$, and
$$\Delta(z_1, \ldots, z_n) = \prod_{i \neq j} |z_i - z_j|.$$

What is the maximum possible value of $\Delta$? Is it maximised by taking the $z_i$
to be the vertices of a regular polygon inscribed in a circle of diameter $2$?

A problem of Erdős, Herzog, and Piranian [EHP58]. Hu and Tang found
counterexamples for $n = 4$ and $n = 6$. Cambie showed that the regular polygon
does not maximise $\Delta$ for any even $n \ge 4$. The question remains open for odd $n$.

[EHP58] Erdős, P., Herzog, F., and Piranian, G., _Metric properties of polynomials_,
J. Analyse Math. 6 (1958), 125–148.
-/

open Complex Finset BigOperators

namespace Erdos1045

/-- The product $\Delta(z) = \prod_{i \neq j} \|z_i - z_j\|$ for a configuration
$z : \mathrm{Fin}\; n \to \mathbb{C}$. -/
noncomputable def erdosDelta (n : ℕ) (z : Fin n → ℂ) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, if i ≠ j then ‖z i - z j‖ else 1

/-- The vertices of a regular $n$-gon inscribed in the unit circle (diameter $2$). -/
noncomputable def regularNGon (n : ℕ) : Fin n → ℂ :=
  fun k => exp (ofReal (2 * Real.pi * (k.val : ℝ) / (n : ℝ)) * I)

/--
Erdős Problem 1045 [EHP58]:

Is it true that for all $n \ge 1$ and all $z_1, \ldots, z_n \in \mathbb{C}$ with
$|z_i - z_j| \le 2$, the product $\Delta(z_1, \ldots, z_n) = \prod_{i \neq j} |z_i - z_j|$
is maximised when the $z_i$ are the vertices of a regular $n$-gon inscribed in a circle
of diameter $2$?

This has been disproved for all even $n \ge 4$ (Hu–Tang, Cambie).
-/
@[category research solved, AMS 30]
theorem erdos_1045 : answer(False) ↔
    ∀ (n : ℕ) (_ : n ≥ 1) (z : Fin n → ℂ) (_ : ∀ i j : Fin n, ‖z i - z j‖ ≤ 2),
      erdosDelta n z ≤ erdosDelta n (regularNGon n) := by
  sorry

/--
The conjecture remains open for odd $n$: for all odd $n \ge 1$ and all
$z_1, \ldots, z_n \in \mathbb{C}$ with $|z_i - z_j| \le 2$, is $\Delta$ maximised by the
regular $n$-gon?
-/
@[category research open, AMS 30]
theorem erdos_1045.variants.odd : answer(sorry) ↔
    ∀ (n : ℕ) (_ : n ≥ 1) (_ : Odd n) (z : Fin n → ℂ)
      (_ : ∀ i j : Fin n, ‖z i - z j‖ ≤ 2),
      erdosDelta n z ≤ erdosDelta n (regularNGon n) := by
  sorry

end Erdos1045
