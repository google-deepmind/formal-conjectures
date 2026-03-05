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
# Erdős Problem 521

Let $(\varepsilon_k)_{k \geq 0}$ be independently uniformly chosen from $\{-1, 1\}$,
and let $R_n$ count the number of real roots of $f_n(z) = \sum_{k=0}^{n} \varepsilon_k z^k$.
Is it true that, almost surely, $\lim_{n \to \infty} R_n / \log n = 2/\pi$?

*Reference:* [erdosproblems.com/521](https://www.erdosproblems.com/521)
-/

open MeasureTheory ProbabilityTheory Polynomial Filter Finset

open scoped BigOperators

namespace Erdos521

/-- The polynomial with prescribed $\pm 1$ coefficients:
$f_n(z) = \sum_{k=0}^{n} \varepsilon(k) \cdot z^k$. -/
noncomputable def signPoly (ε : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ range (n + 1), C (ε k) * X ^ k

/-- The number of distinct real roots of a real polynomial. -/
noncomputable def numRealRoots (p : Polynomial ℝ) : ℕ :=
  Set.ncard {x : ℝ | p.IsRoot x}

/-- A random variable is Rademacher distributed: it takes values in $\{-1, 1\}$
with equal probability (each with probability $1/2$ on a probability space). -/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  (∀ ω, X ω = 1 ∨ X ω = -1) ∧
  μ {ω | X ω = 1} = μ {ω | X ω = -1}

/--
Let $(\varepsilon_k)_{k \geq 0}$ be independently uniformly chosen at random from $\{-1, 1\}$.
If $R_n$ counts the number of real roots of $f_n(z) = \sum_{k=0}^{n} \varepsilon_k z^k$,
then, almost surely, $\lim_{n \to \infty} R_n / \log n = 2/\pi$.

Erdős and Offord showed that the number of real roots of a random degree $n$
polynomial with $\pm 1$ coefficients is $(2/\pi + o(1)) \log n$ in expectation.
This conjecture asks whether the convergence holds almost surely.
-/
@[category research open, AMS 12 60]
theorem erdos_521 : answer(sorry) ↔
    ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
      {ε : ℕ → Ω → ℝ},
    (∀ k, IsRademacher μ (ε k)) →
    iIndepFun ε μ →
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => (numRealRoots (signPoly (fun k => ε k ω) n) : ℝ) / Real.log (n : ℝ))
      atTop (nhds (2 / Real.pi)) := by
  sorry

end Erdos521
