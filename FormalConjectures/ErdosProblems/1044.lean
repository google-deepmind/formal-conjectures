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
# Erdős Problem 1044

*Reference:* [erdosproblems.com/1044](https://www.erdosproblems.com/1044)

Let $f(z) = \prod_{i=1}^{n} (z - z_i)$ be a monic polynomial with all roots in the closed unit
disk. If $\Lambda(f)$ is the maximum of the lengths of the boundaries of the connected components
of $\{z : |f(z)| < 1\}$, determine the infimum of $\Lambda(f)$ over all such $f$.

[EHP58] Erdős, P., Herzog, F., and Piranian, G., *Metric properties of polynomials*,
J. Analyse Math. 6 (1958), 125–148.
-/

open Complex Polynomial MeasureTheory

namespace Erdos1044

/--
The sublevel set $\{z \in \mathbb{C} \mid \|f(z)\| < 1\}$ for a function $f : \mathbb{C} \to \mathbb{C}$.
-/
noncomputable def lemniscateSublevel (f : ℂ → ℂ) : Set ℂ :=
  {z : ℂ | ‖f z‖ < 1}

/--
$\Lambda(f)$: the supremum of the 1-dimensional Hausdorff measures of the frontiers
of the connected components of $\{z \in \mathbb{C} \mid \|f(z)\| < 1\}$. A connected component
containing $x$ in the sublevel set $S$ is `connectedComponentIn S x`.
-/
noncomputable def maxBoundaryLength (f : ℂ → ℂ) : ℝ :=
  sSup {ℓ : ℝ | ∃ x ∈ lemniscateSublevel f,
    ℓ = (Measure.hausdorffMeasure 1
      (frontier (connectedComponentIn (lemniscateSublevel f) x))).toReal}

/--
Erdős Problem 1044 (Erdős–Herzog–Piranian [EHP58]):

Let $f(z) = \prod_{i=1}^{n} (z - z_i) \in \mathbb{C}[z]$ where $|z_i| \leq 1$ for all $i$. If $\Lambda(f)$
is the maximum of the lengths of the boundaries of the connected components
of $\{z : |f(z)| < 1\}$, then the infimum of $\Lambda(f)$ over all such $f$ equals $2$.

Resolved by Tang, who proved that the infimum of $\Lambda(f)$ over all such $f$ is $2$.
-/
@[category research solved, AMS 30]
theorem erdos_1044 :
    sInf {L : ℝ | ∃ (f : Polynomial ℂ), f.Monic ∧ (∀ z, f.IsRoot z → ‖z‖ ≤ 1) ∧
      L = maxBoundaryLength (fun z => Polynomial.eval z f)} = answer((2 : ℝ)) := by
  sorry

end Erdos1044
