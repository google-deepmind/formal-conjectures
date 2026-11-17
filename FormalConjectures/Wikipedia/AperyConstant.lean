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
# Transcendence of Apéry's Constant $\zeta(3)$

Apéry's constant is the cubic reciprocal sum
$$\zeta(3) = \sum_{n=1}^{\infty} \frac{1}{n^3} \approx 1.2020569031$$
([OEIS A002117](https://oeis.org/A002117)). Roger Apéry proved in 1978 [Ap79, vdP79] that
$\zeta(3)$ is irrational (see
`RiemannZetaValues.irrational_three`), using fast-converging rational approximations related to the
alternating series
$$\zeta(3) = \frac{5}{2} \sum_{k=1}^{\infty} \frac{(-1)^{k-1}}{k^3 \binom{2k}{k}}$$
due to Andrey Markov [Ma1890] and M. M. Hjortnaes [Hj53]. Whereas Euler's even-zeta formulas and
Lindemann's theorem imply that $\zeta(2k)$ is transcendental for every $k \ge 1$, transcendence of
$\zeta(3)$ over $\mathbb{Q}$ remains open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Ap%C3%A9ry%27s_constant)
- [Ma1890] A. A. Markov (1890), Mém. Acad. Imp. Sci. St.-Pétersbourg (7) **37**, no. 9, 18 pp.
- [Hj53] M. M. Hjortnaes (1953), Proc. 12th Scand. Math. Congr. (Lund), 211–213.
- [Ap79] R. Apéry (1979), Astérisque **61**, 11–13.
- [vdP79] A. van der Poorten (1979), Math. Intelligencer **1**, no. 4, 195–203.
-/

@[expose] public section

namespace AperyConstant

/-- Apéry's constant $\zeta(3) = \sum_{n=1}^{\infty} \frac{1}{n^3}$ as a real series (the $n = 0$
term vanishes in Lean). -/
noncomputable def aperyConstant : ℝ :=
  ∑' n : ℕ, 1 / (n : ℝ) ^ 3

/-- Coercing `aperyConstant` to `ℂ` recovers `riemannZeta 3`. -/
@[category API, AMS 11 33]
theorem coe_aperyConstant : (aperyConstant : ℂ) = riemannZeta 3 := by
  rw [aperyConstant, Complex.ofReal_tsum, show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num,
    zeta_nat_eq_tsum_of_gt_one (by norm_num : 1 < 3)]
  congr 1
  ext n
  push_cast
  rfl

/-- Transcendence of `riemannZeta 3` over $\mathbb{Q}$ is equivalent to transcendence of
`aperyConstant`. -/
@[category API, AMS 11 33]
theorem transcendental_riemannZeta_three_iff :
    Transcendental ℚ (riemannZeta 3) ↔ Transcendental ℚ aperyConstant := by
  rw [← coe_aperyConstant]
  exact transcendental_algebraMap_iff Complex.ofReal_injective

/-- Apéry's constant $\zeta(3)$ is transcendental over $\mathbb{Q}$. -/
@[category research open, AMS 11 33]
theorem apery_constant_transcendental :
    Transcendental ℚ aperyConstant := by
  sorry

/-- Markov–Hjortnaes–Apéry central-binomial series identity [Ma1890, Hj53, Ap79]:
$\zeta(3) = \frac{5}{2} \sum_{n=0}^{\infty} \frac{(-1)^n}{(n + 1)^3 \binom{2(n + 1)}{n + 1}}$. -/
@[category textbook, AMS 11 33]
theorem apery_central_binomial_series :
    aperyConstant =
      (5 / 2 : ℝ) * ∑' n : ℕ,
        (-1 : ℝ) ^ n / (((n : ℝ) + 1) ^ 3 * (Nat.centralBinom (n + 1) : ℝ)) := by
  sorry

/-- Summing the $n = 1$ and $n = 2$ terms gives `9 / 8 ≤ aperyConstant`. -/
@[category test, AMS 11 33]
theorem nine_eighths_le_aperyConstant : (9 / 8 : ℝ) ≤ aperyConstant := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
  calc (9 / 8 : ℝ) = ∑ n ∈ ({1, 2} : Finset ℕ), 1 / (n : ℝ) ^ 3 := by norm_num
    _ ≤ aperyConstant := hsum.sum_le_tsum {1, 2} (fun _ _ => by positivity)

end AperyConstant
