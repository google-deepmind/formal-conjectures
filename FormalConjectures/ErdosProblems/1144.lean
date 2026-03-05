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
# Erdős Problem 1144

Let $f$ be a random completely multiplicative function, where for each prime $p$ we independently
choose $f(p) \in \{-1, 1\}$ uniformly at random. Is it true that the limsup of
$\sum_{m \leq N} f(m) / \sqrt{N}$ is infinite with probability 1?

*Reference:* [erdosproblems.com/1144](https://www.erdosproblems.com/1144)

[Va99] Vaughan, R.C., *Multiplicative Number Theory I: Classical Theory*. Cambridge Tracts in
Advanced Mathematics, 1999.

[At25] Atherfold, A., *Almost sure upper bounds for random multiplicative functions*, 2025.
-/

open MeasureTheory ProbabilityTheory Filter Finset BigOperators

namespace Erdos1144

/-- A random variable is Rademacher distributed: takes values $\pm 1$ with equal probability. -/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  (∀ ω, X ω = 1 ∨ X ω = -1) ∧
  μ {ω | X ω = 1} = μ {ω | X ω = -1}

/-- The random completely multiplicative function built from Rademacher signs at primes.
For $n \geq 1$: $f(n) = \prod_{p \in \operatorname{primeFactors}(n)} \varepsilon(p)^{v_p(n)}$.
For $n = 0$: $f(0) = 0$. -/
noncomputable def randMultFun {Ω : Type*} (ε : ℕ → Ω → ℝ) (ω : Ω) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else ∏ p ∈ n.factorization.support, (ε p ω) ^ (n.factorization p)

/-- The partial sum $\sum_{m=1}^{N} f(m)$. -/
noncomputable def partialSum {Ω : Type*} (ε : ℕ → Ω → ℝ) (ω : Ω) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, randMultFun ε ω m

/--
Erdős Problem 1144 [Va99, 1.11]:

Let $f$ be a random completely multiplicative function, where for each prime $p$
we independently choose $f(p) \in \{-1, 1\}$ uniformly at random. Is it true that
$$\limsup_{N \to \infty} \frac{\sum_{m \leq N} f(m)}{\sqrt{N}} = \infty$$
with probability 1?

This model is sometimes called a Rademacher random multiplicative function.
Atherfold [At25] proved that, almost surely,
$$\sum_{m \leq N} f(m) \ll N^{1/2} (\log N)^{1+o(1)}.$$
-/
@[category research open, AMS 11 60]
theorem erdos_1144 :
    answer(sorry) ↔
    ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ε : ℕ → Ω → ℝ),
      (∀ k, IsRademacher μ (ε k)) →
      iIndepFun ε μ →
      (∀ᵐ ω ∂μ, ∀ C : ℝ,
        ∃ᶠ N in atTop,
          partialSum ε ω N > C * Real.sqrt (N : ℝ)) := by
  sorry

end Erdos1144
