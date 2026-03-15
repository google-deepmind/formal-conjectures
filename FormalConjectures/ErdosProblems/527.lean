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
# Erdős Problem 527

*Reference:* [erdosproblems.com/527](https://www.erdosproblems.com/527)

Let $a_n \in \mathbb{R}$ with $\sum |a_n|^2 = \infty$ and $|a_n| = o(1/\sqrt{n})$.
Is it true that, for almost all choices of signs $\varepsilon_n = \pm 1$, there exists
some $z$ with $|z| = 1$ such that $\sum \varepsilon_n a_n z^n$ converges?
Solved affirmatively by Michelen and Sawhney.

[DE59] Dvoretzky, A. and Erdős, P., *Divergence of random power series*, Michigan Math. J.
(1959), 343–347.

[Er61] Erdős, P., *Some unsolved problems*, Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
p.254.

[MiSa25] Michelen, M. and Sawhney, M., *Convergent points for random power series on the
unit circle*, arXiv:2509.02729 (2025).
-/

open MeasureTheory ProbabilityTheory Filter Finset BigOperators

namespace Erdos527

/-- A random variable is Rademacher distributed: it takes values in $\{-1, 1\}$
with equal probability. -/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  (∀ ω, X ω = 1 ∨ X ω = -1) ∧
  μ {ω | X ω = 1} = μ {ω | X ω = -1}

/-- The partial sum of the random power series $\sum_{k=0}^{n-1} \varepsilon_k a_k z^k$. -/
noncomputable def randomPowerPartialSum (ε : ℕ → ℝ) (a : ℕ → ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n, ((ε k * a k : ℝ) : ℂ) * z ^ k

/--
Erdős Problem 527 [Er61, p.254]:

Let $a_n \in \mathbb{R}$ be such that $\sum |a_n|^2 = \infty$ and $|a_n| = o(1/\sqrt{n})$.
Is it true that, for almost all $\varepsilon_n = \pm 1$, there exists some $z$ with $|z| = 1$
(depending on the choice of signs) such that $\sum \varepsilon_n a_n z^n$ converges?

It is unclear whether Erdős intended to also assume monotonicity $|a_{n+1}| \leq |a_n|$;
the formalization omits this assumption, matching the stronger result of Michelen and
Sawhney [MiSa25], who proved the statement without monotonicity and showed that the set
of such $z$ has Hausdorff dimension 1. Dvoretzky and Erdős [DE59] showed that if
$|a_n| > c/\sqrt{n}$ for some $c > 0$, then the series diverges almost surely at every
$|z| = 1$, so the $o(1/\sqrt{n})$ condition is essentially sharp.
-/
@[category research solved, AMS 40 60]
theorem erdos_527 : answer(True) ↔
    ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
      {ε : ℕ → Ω → ℝ},
    (∀ k, IsRademacher μ (ε k)) → iIndepFun ε μ →
    ∀ (a : ℕ → ℝ), ¬Summable (fun n => a n ^ 2) →
    Tendsto (fun n => |a n| * Real.sqrt (↑n : ℝ)) atTop (nhds 0) →
    ∀ᵐ ω ∂μ, ∃ z : ℂ, ‖z‖ = 1 ∧
      ∃ S : ℂ, Tendsto (randomPowerPartialSum (fun k => ε k ω) a z) atTop (nhds S) := by
  sorry

end Erdos527
