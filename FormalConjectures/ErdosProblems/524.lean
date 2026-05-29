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
# Erdős Problem 524

A problem of Salem and Zygmund [SaZy54]. For any $t \in (0,1)$ let
$t = \sum_{k=1}^{\infty} \varepsilon_k(t) 2^{-k}$ be the binary expansion (where
$\varepsilon_k(t) \in \{0,1\}$). What is the correct order of magnitude (for almost all
$t \in (0,1)$) of
$$M_n(t) = \max_{x \in [-1,1]} \left|\sum_{k \le n} (-1)^{\varepsilon_k(t)} x^k\right|?$$

The binary digits $\varepsilon_k(t)$ are i.i.d. Bernoulli$(1/2)$ under Lebesgue measure, so
$(-1)^{\varepsilon_k(t)}$ are i.i.d. Rademacher random variables.

**Known partial results:**
- Erdős showed: for a.a. $t$ and every $\delta > 0$,
  $\limsup_{n \to \infty} M_n(t)/n^{1/2 - \delta} = \infty$.
- Chung showed: for a.a. $t$, there exist infinitely many $n$ such that
  $M_n(t) \ll (n / \log \log n)^{1/2}$.

## References

[Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int.
Közl. **6** (1961), 221–254, p.253.

[SaZy54] Salem, R., Zygmund, A., _Some properties of trigonometric series whose
terms have random signs_. Acta Mathematica (1954), 245–301.

*Reference:* [erdosproblems.com/524](https://www.erdosproblems.com/524)
-/

open MeasureTheory ProbabilityTheory Filter Finset BigOperators Set Asymptotics

namespace Erdos524

/-- A random variable is Rademacher distributed: it takes values in $\{-1, 1\}$
with equal probability. -/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  (∀ ω, X ω = 1 ∨ X ω = -1) ∧
  μ {ω | X ω = 1} = μ {ω | X ω = -1}

/-- The supremum of $\left|\sum_{k=1}^n \varepsilon_k x^k\right|$ over $x \in [-1, 1]$. -/
noncomputable def supNormInterval (ε : ℕ → ℝ) (n : ℕ) : ℝ :=
  sSup {y : ℝ | ∃ x : ℝ, x ∈ Icc (-1 : ℝ) 1 ∧
    y = |∑ k ∈ Finset.range n, ε (k + 1) * x ^ (k + 1)|}

/-- What is the correct order of magnitude of $M_n(t)$ for almost all $t$?
The answer $f : \mathbb{N} \to \mathbb{R}$ should satisfy
$M_n(\omega) =\Theta(f(n))$ as $n \to \infty$ for a.a. $\omega$. -/
@[category research open, AMS 42 60]
theorem erdos_524
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ε : ℕ → Ω → ℝ}
    (hRad : ∀ k, IsRademacher μ (ε k))
    (hIndep : iIndepFun ε μ) :
    ∀ᵐ ω ∂μ,
      (fun n => supNormInterval (fun k => ε k ω) n) =Θ[atTop]
        (answer(sorry) : ℕ → ℝ) := by
  sorry

/-- Erdős showed that for almost all $\omega$ and every $\delta > 0$,
$\limsup_{n \to \infty} M_n(\omega) / n^{1/2 - \delta} = \infty$. -/
@[category research solved, AMS 42 60]
theorem erdos_524.variants.lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ε : ℕ → Ω → ℝ}
    (hRad : ∀ k, IsRademacher μ (ε k))
    (hIndep : iIndepFun ε μ) :
    ∀ᵐ ω ∂μ, ∀ δ > (0 : ℝ), ∀ C > (0 : ℝ),
      ∃ᶠ n in atTop,
        C ≤ supNormInterval (fun k => ε k ω) n /
          (↑n : ℝ) ^ ((1 : ℝ)/2 - δ) := by
  sorry

/-- Chung showed that for almost all $\omega$, there exist infinitely many $n$ such that
$M_n(\omega) \ll (n / \log \log n)^{1/2}$. -/
@[category research solved, AMS 42 60]
theorem erdos_524.variants.upper_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ε : ℕ → Ω → ℝ}
    (hRad : ∀ k, IsRademacher μ (ε k))
    (hIndep : iIndepFun ε μ) :
    ∃ C > (0 : ℝ), ∀ᵐ ω ∂μ,
      ∃ᶠ n in atTop,
        supNormInterval (fun k => ε k ω) n ≤
          C * ((↑n : ℝ) / Real.log (Real.log (↑n : ℝ))) ^ ((1 : ℝ)/2) := by
  sorry

end Erdos524
