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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 1039

*References:*
- [erdosproblems.com/1039](https://www.erdosproblems.com/1039)
- [EHP58] P. Erdős, F. Herzog and G. Piranian, *Metric properties of polynomials*,
  J. Analyse Math. 6 (1958), 125–148.
- [Po61] Ch. Pommerenke, *On metric properties of complex polynomials*, Michigan Math. J. 8
  (1961), 97–115.
- [KLR25] M. Krishnapur, E. Lundberg and K. Ramachandran, *On the area of polynomial
  lemniscates*, [arXiv:2503.18270](https://arxiv.org/abs/2503.18270) (2025).
-/

@[expose] public section

namespace Erdos1039

/-- The radius $\rho$ of the largest open disc contained in $\{w : \lvert\prod_i (w - z_i)\rvert < 1\}$.
-/
noncomputable def ρ {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  sSup {r : ℝ | ∃ c : ℂ, Metric.ball c r ⊆ {w : ℂ | ‖∏ i, (w - z i)‖ < 1}}

/--
Let $f(z) = \prod_{i=1}^n (z - z_i) \in \mathbb{C}[z]$ with $\lvert z_i\rvert \le 1$ for all $i$.
Let $\rho(f)$ be the radius of the largest disc contained in $\{z : \lvert f(z)\rvert < 1\}$.
Is $\rho(f) \gg 1/n$?
-/
@[category research open, question, AMS 30]
theorem erdos_1039 : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
    ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ 1) → c / n ≤ ρ z := by
  sorry

/-- Erdős, Herzog and Piranian [EHP58]: for $f(z) = z^n - 1$, $\rho(f) \le (\pi/2)/n$. Here the
$z_i$ are the $n$-th roots of unity. So $1/n$ would be the right order. -/
@[category research solved, AMS 30]
theorem erdos_1039.variants.roots_of_unity (n : ℕ) (hn : 1 ≤ n) :
    ρ (fun i : Fin n => Complex.exp (2 * Real.pi * Complex.I * i / n)) ≤ Real.pi / 2 / n := by
  sorry

/-- Pommerenke [Po61]: $\rho(f) \ge \frac{1}{2en^2}$. -/
@[category research solved, AMS 30]
theorem erdos_1039.variants.pommerenke (n : ℕ) (hn : 1 ≤ n) (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) : 1 / (2 * Real.exp 1 * n ^ 2) ≤ ρ z := by
  sorry

/-- Krishnapur, Lundberg and Ramachandran [KLR25]: $\rho(f) \gg \frac{1}{n\sqrt{\log n}}$. -/
@[category research solved, AMS 30]
theorem erdos_1039.variants.klr : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
    ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ 1) → c / (n * Real.sqrt (Real.log n)) ≤ ρ z := by
  sorry

end Erdos1039
