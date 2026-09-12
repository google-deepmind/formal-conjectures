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

import FormalConjecturesUtil

/-!
# Erdős Problem 1039

*References:*
- [erdosproblems.com/1039](https://www.erdosproblems.com/1039)
- [EHP58] Erdős, P. and Herzog, F. and Piranian, G., *Metric properties of polynomials*.
  J. Analyse Math. (1958), 125-148.
- [KLR25] M. Krishnapur, E. Lundberg, and K. Ramachandran, *On the area of polynomial
  lemniscates*. arXiv:2503.18270 (2025).
- [Po61] Pommerenke, Ch., *On metric properties of complex polynomials*. Michigan Math. J.
  (1961), 97-115.
-/

open Polynomial

namespace Erdos1039

/--
The polynomials under consideration: those of the form $f(z)=\prod_{i=1}^n(z-z_i)$, for some
$n\geq 1$, where $\lvert z_i\rvert\leq 1$ for all $i$.
-/
def IsAdmissible (f : ℂ[X]) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ 1) ∧ f = ∏ i, (X - C (z i))

/-- The open filled lemniscate $\{z : \lvert f(z)\rvert < 1\}$. -/
def openLemniscate (f : ℂ[X]) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ < 1}

/--
$\rho(f)$, the inradius of $\{z : \lvert f(z)\rvert < 1\}$: the radius of the largest disc
contained in the open filled lemniscate.
-/
noncomputable def rho (f : ℂ[X]) : ℝ :=
  sSup {r : ℝ | ∃ c : ℂ, Metric.ball c r ⊆ openLemniscate f}

/-- The infimal inradius among admissible polynomials of degree $n$. -/
noncomputable def minRho (n : ℕ) : ℝ :=
  sInf (rho '' {f : ℂ[X] | IsAdmissible f ∧ f.natDegree = n})

/--
Let $f(z)=\prod_{i=1}^n(z-z_i)\in \mathbb{C}[z]$ with $\lvert z_i\rvert \leq 1$ for all $i$.
Let $\rho(f)$ be the radius of the largest disc which is contained in
$\{z: \lvert f(z)\rvert< 1\}$.

Determine the behaviour of $\rho(f)$. In particular, is it always true that $\rho(f)\gg 1/n$?

A problem of Erdős, Herzog, and Piranian [EHP58].
-/
@[category research open, AMS 12 30]
theorem erdos_1039 : answer(sorry) ↔ minRho ≫ fun n ↦ 1 / (n : ℝ) := by
  sorry

/--
Pommerenke [Po61] proved that
$$\rho(f) \geq \frac{1}{2en^2}.$$
-/
@[category research solved, AMS 12 30]
theorem erdos_1039.variants.pommerenke {n : ℕ} {f : ℂ[X]} (hn : 0 < n)
    (hf : IsAdmissible f) (hdeg : f.natDegree = n) :
    1 / (2 * Real.exp 1 * n ^ 2) ≤ rho f := by
  sorry

/--
Krishnapur, Lundberg, and Ramachandran [KLR25] proved
$$\rho(f) \gg \frac{1}{n\sqrt{\log n}}.$$
-/
@[category research solved, AMS 12 30]
theorem erdos_1039.variants.krishnapur_lundberg_ramachandran :
    minRho ≫ fun n ↦ 1 / (n * Real.sqrt (Real.log n)) := by
  sorry

/--
A problem of Erdős, Herzog, and Piranian, who note that $f(z)=z^n-1$ has
$\rho(f) \leq \frac{\pi/2}{n}$.
-/
@[category research solved, AMS 12 30]
theorem erdos_1039.variants.erdos_lemniscate {n : ℕ} (hn : 0 < n) :
    rho ((X : ℂ[X]) ^ n - 1) ≤ (Real.pi / 2) / n := by
  sorry

end Erdos1039
