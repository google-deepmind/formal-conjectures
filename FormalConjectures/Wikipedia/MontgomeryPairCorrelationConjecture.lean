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
# Montgomery's GUE pair correlation conjecture for zeta zeros

Hugh L. Montgomery (1973) studied vertical spacings among critical-line zeros $1/2 + i\gamma$ of
$\zeta(s)$ assuming `RiemannHypothesis`, observing with Freeman Dyson that their predicted two-point
density matches Gaussian Unitary Ensemble (GUE) eigenvalue pair statistics. Counting positive
ordinates $0 < \gamma, \gamma' \le T$ with multiplicity, Montgomery conjectured that for fixed
$0 < \alpha < \beta$,
$$\lim_{T \to \infty}
  \frac{\#\left\{(\gamma, \gamma') \in (0, T]^2 :
    \frac{2\pi\alpha}{\log T} \le \gamma - \gamma' \le \frac{2\pi\beta}{\log T}\right\}}
  {\frac{T}{2\pi} \log T}
  = \int_\alpha^\beta \left(1 - \operatorname{sinc}(\pi u)^2\right) du,$$
and more generally for all $\alpha \le \beta$ with an added point-mass term $\mathbf{1}_{0 \in
[\alpha, \beta]}$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Montgomery%27s_pair_correlation_conjecture)
- H. L. Montgomery, *The pair correlation of zeros of the zeta function*, Proc. Sympos. Pure Math.
  **24**, Amer. Math. Soc., 1973, 181–193.
-/

@[expose] public section

namespace MontgomeryPairCorrelationConjecture

/-- Order of vanishing of $\zeta(s)$ at $s = 1/2 + i\gamma$ ($0$ when
$\zeta(1/2 + i\gamma) \neq 0$). -/
noncomputable def zetaCriticalZeroMultiplicity (γ : ℝ) : ℕ :=
  Complex.zeroCountOn riemannZeta {(1 / 2 : ℂ) + Complex.I * (γ : ℂ)}

/-- Multiplicity-weighted count of ordered ordinate pairs $(\gamma_1, \gamma_2) \in (0, T]^2$ of
critical-line zeros of $\zeta(s)$ satisfying
$\frac{2\pi\alpha}{\log T} \le \gamma_1 - \gamma_2 \le \frac{2\pi\beta}{\log T}$. -/
noncomputable def zetaPairCorrelationCount (T α β : ℝ) : ℕ :=
  ∑ᶠ γ₂ ∈ Set.Ioc 0 T,
    zetaCriticalZeroMultiplicity γ₂ *
      Complex.zeroCountOn riemannZeta
        {s : ℂ | s.re = 1 / 2 ∧ s.im ∈ Set.Ioc 0 T ∧
          2 * Real.pi * α / Real.log T ≤ s.im - γ₂ ∧
          s.im - γ₂ ≤ 2 * Real.pi * β / Real.log T}

/-- Dyson–Montgomery GUE two-point correlation kernel $1 - \operatorname{sinc}(\pi u)^2$,
continuously extended by `0` at $u = 0$. -/
noncomputable def guePairKernel (u : ℝ) : ℝ :=
  1 - Real.sinc (Real.pi * u) ^ 2

/-- At $u = 0$, `guePairKernel` vanishes. -/
@[category test, AMS 11 30]
theorem guePairKernel_zero : guePairKernel 0 = 0 := by
  simp [guePairKernel]

/-- At $u = 1$, `guePairKernel` equals $1$. -/
@[category test, AMS 11 30]
theorem guePairKernel_one : guePairKernel 1 = 1 := by
  simp [guePairKernel, Real.sinc_of_ne_zero Real.pi_ne_zero]

/-- The GUE pair correlation kernel `guePairKernel` is even and takes values in $[0, 1]$. -/
@[category API, AMS 11 30]
theorem guePairKernel_even_and_mem_Icc (u : ℝ) :
    guePairKernel (-u) = guePairKernel u ∧ 0 ≤ guePairKernel u ∧ guePairKernel u ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold guePairKernel
    by_cases hu : u = 0
    · simp [hu]
    · have h1 : Real.pi * -u ≠ 0 := mul_ne_zero Real.pi_ne_zero (neg_ne_zero.mpr hu)
      have h2 : Real.pi * u ≠ 0 := mul_ne_zero Real.pi_ne_zero hu
      rw [Real.sinc_of_ne_zero h1, Real.sinc_of_ne_zero h2, mul_neg, Real.sin_neg, neg_div_neg_eq]
  · unfold guePairKernel
    obtain ⟨h1, h2⟩ := abs_le.mp (Real.abs_sinc_le_one (Real.pi * u))
    nlinarith
  · unfold guePairKernel
    linarith [sq_nonneg (Real.sinc (Real.pi * u))]

/-- Any ordinate $\gamma$ with $\zeta(1/2 + i\gamma) \neq 0$ has multiplicity $0$. -/
@[category API, AMS 11 30]
theorem zetaCriticalZeroMultiplicity_eq_zero_of_ne_zero {γ : ℝ}
    (h : riemannZeta ((1 / 2 : ℂ) + Complex.I * (γ : ℂ)) ≠ 0) :
    zetaCriticalZeroMultiplicity γ = 0 := by
  rw [zetaCriticalZeroMultiplicity, Complex.zeroCountOn_singleton]
  exact Complex.analyticOrderNatAt_eq_zero_of_ne_zero h

/-- `zetaPairCorrelationCount T α β` vanishes whenever $T \le 0$. -/
@[category API, AMS 11 30]
theorem zetaPairCorrelationCount_eq_zero_of_nonpos {T α β : ℝ} (hT : T ≤ 0) :
    zetaPairCorrelationCount T α β = 0 := by
  unfold zetaPairCorrelationCount
  rw [Set.Ioc_eq_empty (not_lt.mpr hT), finsum_mem_empty]

/-- Montgomery's Pair Correlation Conjecture (1973): given `RiemannHypothesis`, for every
$0 < \alpha < \beta$, the normalized pair count of critical-line zeros of $\zeta(s)$ in $(0, T]$
with normalized spacing in $[\alpha, \beta]$ converges to
$\int_\alpha^\beta \left(1 - \operatorname{sinc}(\pi u)^2\right) du$ as $T \to \infty$. -/
@[category research open, AMS 11 30]
theorem montgomery_pair_correlation_conjecture (hRH : RiemannHypothesis)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    Filter.Tendsto
      (fun T : ℝ => (zetaPairCorrelationCount T α β : ℝ) / ((T / (2 * Real.pi)) * Real.log T))
      Filter.atTop
      (nhds (∫ u in α..β, guePairKernel u)) := by
  sorry

open scoped Classical in
/-- General-interval form of Montgomery's Pair Correlation Conjecture: given `RiemannHypothesis`,
for any fixed $\alpha \le \beta$, the normalized pair count converges to
$\int_\alpha^\beta \left(1 - \operatorname{sinc}(\pi u)^2\right) du + \mathbf{1}_{0 \in [\alpha,
\beta]}$ as $T \to \infty$. -/
@[category research open, AMS 11 30]
theorem montgomery_pair_correlation_conjecture.variants.general_interval
    (hRH : RiemannHypothesis) (α β : ℝ) (hαβ : α ≤ β) :
    Filter.Tendsto
      (fun T : ℝ => (zetaPairCorrelationCount T α β : ℝ) / ((T / (2 * Real.pi)) * Real.log T))
      Filter.atTop
      (nhds ((∫ u in α..β, guePairKernel u) + if (0 : ℝ) ∈ Set.Icc α β then 1 else 0)) := by
  sorry

end MontgomeryPairCorrelationConjecture
