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
# Erdős Problem 1045

*References:*
- [erdosproblems.com/1045](https://www.erdosproblems.com/1045)
- [EHP58] P. Erdős, F. Herzog and G. Piranian, *Metric properties of polynomials*,
  J. Analyse Math. 6 (1958), 125–148.
- [Po61] Ch. Pommerenke, *On metric properties of complex polynomials*, Michigan Math. J. 8
  (1961), 97–115.
- [So25] N. Sothanaphan, *An improved lower bound to Erdős' problem concerning products of
  distances for fixed diameter*, [arXiv:2512.14251](https://arxiv.org/abs/2512.14251) (2025).
- [CDDHT26] S. Cambie, A. Decadt, Y. Dong, T. Hu and Q. Tang, *On the maximum product of distances
  of diameter $2$ point sets*, [arXiv:2603.07088](https://arxiv.org/abs/2603.07088) (2026).
-/

@[expose] public section

open Filter Topology

namespace Erdos1045

/-- $\Delta(z_1, \ldots, z_n) = \prod_{i \ne j} \lvert z_i - z_j\rvert$, over ordered pairs. -/
noncomputable def Δ {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∏ i, ∏ j ∈ Finset.univ.erase i, ‖z i - z j‖

/-- The maximum of $\Delta$ over $z_1, \ldots, z_n$ with $\lvert z_i - z_j\rvert \le 2$. -/
noncomputable def M (n : ℕ) : ℝ :=
  sSup {d | ∃ z : Fin n → ℂ, (∀ i j, ‖z i - z j‖ ≤ 2) ∧ Δ z = d}

def erdos_1045.answer : ℕ → ℝ := by sorry

/--
Let $z_1, \ldots, z_n \in \mathbb{C}$ with $\lvert z_i - z_j\rvert \le 2$ for all $i, j$. What is
the maximum possible value of $\Delta(z_1, \ldots, z_n) = \prod_{i \ne j} \lvert z_i - z_j\rvert$?
-/
@[category research open, question value, AMS 30 52]
theorem erdos_1045 (n : ℕ) : M n = erdos_1045.answer n := by
  sorry

/--
Is the maximum attained by the vertices of a regular polygon? For even $n$ these give
$\Delta = n^n$. Cambie, Hu and Tang showed on the problem page that for every even $n \ge 4$
the regular polygon is not a maximiser (see [So25] and [CDDHT26]).
-/
@[category research solved, AMS 30 52]
theorem erdos_1045.variants.even (n : ℕ) (hn : 4 ≤ n) (heven : Even n) :
    (n : ℝ) ^ n < M n := by
  sorry

/--
For odd $n$ the regular polygon of diameter $2$ gives $\Delta = \cos(\pi/2n)^{-n(n-1)} n^n$.
Cambie, Decadt, Dong, Hu and Tang [CDDHT26] conjecture that it is a maximiser for odd $n$.
-/
@[category research open, AMS 30 52]
theorem erdos_1045.variants.odd (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    M n = Real.cos (Real.pi / (2 * n)) ^ (-((n : ℝ) * (n - 1))) * (n : ℝ) ^ n := by
  sorry

/-- Is $\lim M(n) / n^n = e^{\pi^2/8}$ as $n \to \infty$ through odd $n$? This would follow from
`erdos_1045.variants.odd`. -/
@[category research open, AMS 30 52]
theorem erdos_1045.variants.odd_limit :
    Tendsto (fun k : ℕ => M (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) ^ (2 * k + 1)) atTop
      (𝓝 (Real.exp (Real.pi ^ 2 / 8))) := by
  sorry

/-- Pommerenke [Po61]: $\Delta \le 2^{O(n)} n^n$. -/
@[category research solved, AMS 30 52]
theorem erdos_1045.variants.pommerenke :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → M n ≤ C ^ n * (n : ℝ) ^ n := by
  sorry

end Erdos1045
