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

Erdős–Herzog–Piranian conjecture: the arc length of the level curve
$\{z \in \mathbb{C} : |p(z)| = 1\}$ of a monic polynomial of degree $n$ is maximized when
$p(z) = z^n - 1$.

Also appears as Problem 4.10 in [Ha74], attributed to Erdős.

[EHP58] Erdős, P., Herzog, F. and Piranian, G., _Metric properties of polynomials_,
J. Analyse Math. 6 (1958), 125–148.

[Po59] Pommerenke, Ch., _On some problems by Erdős, Herzog and Piranian_,
Michigan Math. J. 6 (1959), 221–225.

[Po61] Pommerenke, Ch., _On metric properties of complex polynomials_,
Michigan Math. J. 8 (1961), 97–115.

[Ha74] Hayman, W. K., _Research problems in function theory: new problems_, (1974), 155–180.

[Va99] _Some of Paul's favorite problems_, Booklet, Conference "Paul Erdős and his
mathematics", Budapest, July 1999.
-/

open scoped ENNReal

open Polynomial MeasureTheory

namespace Erdos114

/-- The unit level curve of a complex polynomial $p$: the set of $z \in \mathbb{C}$ with
$|p(z)| = 1$. -/
def levelCurveUnit (p : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ = 1}

/-- The arc length of a subset of $\mathbb{C}$, given by the 1-dimensional Hausdorff measure. -/
noncomputable def arcLength (S : Set ℂ) : ℝ≥0∞ :=
  Measure.hausdorffMeasure 1 S

/--
Erdős–Herzog–Piranian Conjecture (Problem #114) [EHP58]:
If $p(z) \in \mathbb{C}[z]$ is a monic polynomial of degree $n \geq 1$, then the length of the
curve $\{z \in \mathbb{C} : |p(z)| = 1\}$ is maximized when $p(z) = z^n - 1$.

That is, for every monic polynomial $p$ of degree $n$,
$$\mathrm{length}(\{z : |p(z)| = 1\}) \leq \mathrm{length}(\{z : |z^n - 1| = 1\}).$$

Known partial results:
- The curve for $p(z) = z^n - 1$ has length $2n + O(1)$, so the conjecture implies
  the maximal length $f(n)$ satisfies $f(n) = 2n + O(1)$.
- Pommerenke (1961) [Po61]: $f(n) \ll n^2$.
- Dolzhenko (1961): $f(n) \leq 4\pi n$.
- Borwein (1995): $f(n) \ll n$.
- Eremenko–Hayman (1999): $f(n) \leq 9.173n$; full conjecture holds for $n = 2$.
- Vayman (1999) [Va99]: asked whether $f(n) \leq 2n + O(1)$.
- Danchenko (2007): $f(n) \leq 2\pi n$.
- Fryntov–Nazarov (2009): $f(n) \leq 2n + O(n^{7/8})$; $z^n - 1$ is a local maximiser.
- Tao (2025): $z^n - 1$ is the unique maximiser (up to rotation and translation) for all
  sufficiently large $n$.
-/
@[category research open, AMS 30]
theorem erdos_114 :
    ∀ n : ℕ, 1 ≤ n →
    ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
      arcLength (levelCurveUnit p) ≤
      arcLength (levelCurveUnit ((X : Polynomial ℂ) ^ n - 1)) := by
  sorry

/--
Tao (2025) [Ta25]: The Erdős–Herzog–Piranian conjecture holds for all sufficiently large $n$.
That is, there exists $N$ such that for all $n \geq N$ and all monic polynomials $p$ of degree $n$,
the arc length of $\{z : |p(z)| = 1\}$ is at most that of $\{z : |z^n - 1| = 1\}$.
-/
@[category research solved, AMS 30]
theorem erdos_114_large_n :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
      arcLength (levelCurveUnit p) ≤
      arcLength (levelCurveUnit ((X : Polynomial ℂ) ^ n - 1)) := by
  sorry

/--
Eremenko–Hayman (1999) [ErHa99]: The Erdős–Herzog–Piranian conjecture holds for $n = 2$.
-/
@[category research solved, AMS 30]
theorem erdos_114_deg_two :
    ∀ p : Polynomial ℂ, p.Monic → p.natDegree = 2 →
      arcLength (levelCurveUnit p) ≤
      arcLength (levelCurveUnit ((X : Polynomial ℂ) ^ 2 - 1)) := by
  sorry

/--
Fryntov–Nazarov (2009) [FrNa09]: For all monic polynomials $p$ of degree $n$, the arc length
of $\{z : |p(z)| = 1\}$ is at most $2n + O(n^{7/8})$.
-/
@[category research solved, AMS 30]
theorem erdos_114_upper_bound :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
      arcLength (levelCurveUnit p) ≤ ENNReal.ofReal (2 * n + C * n ^ (7 / 8 : ℝ)) := by
  sorry

/--
Pommerenke (1959) [Po59]: If $p$ is a monic polynomial of degree $n$ and the sublevel set
$\{z : |p(z)| < 1\}$ is connected, then the arc length of $\{z : |p(z)| = 1\}$ is at least $2\pi$.
-/
@[category research solved, AMS 30]
theorem erdos_114_pommerenke_lower_bound :
    ∀ n : ℕ, 1 ≤ n →
    ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
      IsConnected {z : ℂ | ‖p.eval z‖ < 1} →
      ENNReal.ofReal (2 * Real.pi) ≤ arcLength (levelCurveUnit p) := by
  sorry

end Erdos114
