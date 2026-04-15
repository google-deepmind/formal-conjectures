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
# Erdős Problem 114

*Reference:* [erdosproblems.com/114](https://www.erdosproblems.com/114)

The **Erdős–Herzog–Piranian (EHP) conjecture** (1958): among all monic polynomials
$p$ of degree $n$, the arc length of the lemniscate $\{z \in \mathbb{C} \mid |p(z)| = 1\}$
is maximised uniquely by $p(z) = z^n - c$, $|c| = 1$.

### Known partial results

- **$n = 2$**: Eremenko–Hayman (1999) [EH99]
- **$3 \leq n \leq 14$**: Mendoza (2026), IEEE 1788-rigorous interval arithmetic,
  [doi:10.5281/zenodo.19480329](https://doi.org/10.5281/zenodo.19480329)
- **Sufficiently large $n$**: Tao (2025) [Ta25]
- **Upper bound**: $L(p) \leq 2\pi n$ for all monic degree-$n$ $p$ (Pommerenke, 1961)

### References

- [EHP58] Erdős, P., Herzog, F., Piranian, G. (1958). *Metric properties of polynomials*.
  J. Analyse Math. 6, 125–148.
- [Po61] Pommerenke, Ch. (1961). *Über die Kapazität ebener Kontinuen*.
  Math. Ann. 144, 115–120.
- [EH99] Eremenko, A., Hayman, W. (1999). *On the length of lemniscates*.
  Michigan Math. J. 46, 409–415.
- [Ta25] Tao, T. (2025). *The Erdős–Herzog–Piranian conjecture for large $n$*.

### AI disclosure

Lean 4 code in this file was drafted with assistance from Claude (Anthropic).
The mathematical content, computational verification, and certificates are the
author's own work.
-/

open Polynomial MeasureTheory ENNReal Classical

namespace Erdos114

/-- The level curve (lemniscate) of a polynomial `p` at level 1:
$\{z \in \mathbb{C} \mid \|p(z)\| = 1\}$. -/
def levelCurveUnit (p : ℂ[X]) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ = 1}

/-- The arc length of the lemniscate of `p`, measured as the
1-dimensional Hausdorff measure of the level curve. -/
noncomputable def arcLength (p : ℂ[X]) : ℝ≥0∞ :=
  μH[1] (levelCurveUnit p)

/-- **Erdős Problem 114** (open conjecture). Among all monic polynomials of
degree $n$, $p(z) = z^n - c$ (with $|c| = 1$) maximises the arc length of the
lemniscate $\{z \in \mathbb{C} \mid |p(z)| = 1\}$.

Originally posed by Erdős, Herzog, and Piranian [EHP58]. Solved for $n = 2$
[EH99], $3 \leq n \leq 14$ (Mendoza, 2026), and sufficiently large $n$ [Ta25].
Open in general. -/
@[category research open, AMS 30]
theorem erdos_114 (n : ℕ) (hn : 1 ≤ n)
    (p : ℂ[X]) (hp : p.Monic) (hp_deg : p.natDegree = n) :
    arcLength p ≤ arcLength (X ^ n - C 1) := by
  sorry

/-- **Erdős Problem 114, small $n$** (solved, computationally certified).
For $3 \leq n \leq 14$, the polynomial $z^n - c$ ($|c| = 1$) maximises the arc
length of the lemniscate among all monic polynomials of degree $n$.

Verified by IEEE 1788-rigorous interval arithmetic using branch-and-bound
(Python/mpmath for $n \leq 12$, Rust/inari for $n \leq 14$). Each case reduces
to a finite computation over a compact parameter space, with all bounds certified
to floating-point rigor per IEEE 1788-2015.

*Reference:* K. Mendoza (2026).
[doi:10.5281/zenodo.19480329](https://doi.org/10.5281/zenodo.19480329) -/
@[category research solved, AMS 30]
theorem erdos_114_small_n (n : ℕ) (hn : 3 ≤ n) (hn14 : n ≤ 14)
    (p : ℂ[X]) (hp : p.Monic) (hp_deg : p.natDegree = n) :
    arcLength p ≤ arcLength (X ^ n - C 1) := by
  sorry

end Erdos114
