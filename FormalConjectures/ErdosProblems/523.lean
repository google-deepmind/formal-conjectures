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
# Erdős Problem 523

Erdős asked whether the supremum of a random Rademacher polynomial on the unit
circle is asymptotically $C\sqrt{n \log n}$ for some constant $C > 0$.

*Reference:* [erdosproblems.com/523](https://www.erdosproblems.com/523)
-/

open MeasureTheory ProbabilityTheory Filter Finset

open scoped BigOperators

namespace Erdos523

/-- A random variable is Rademacher distributed: it takes values in $\{-1, 1\}$
with equal probability. -/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  (∀ ω, X ω = 1 ∨ X ω = -1) ∧
  μ {ω | X ω = 1} = μ {ω | X ω = -1}

/-- The supremum of $|\sum_{k=0}^n \varepsilon_k z^k|$ over the unit circle $|z| = 1$. -/
noncomputable def supNormCircle (ε : ℕ → ℝ) (n : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧
    x = ‖(∑ k ∈ Finset.range (n + 1), (ε k : ℂ) * z ^ k)‖}

/--
Erdős Problem #523:
Let $f(z) = \sum_{k=0}^n \varepsilon_k z^k$ be a random polynomial, where
$\varepsilon_k \in \{-1, 1\}$ independently uniformly at random.

Does there exist some constant $C > 0$ such that, almost surely,
$$\max_{|z|=1} \left|\sum_{k \le n} \varepsilon_k z^k\right| = (C + o(1))\sqrt{n \log n}?$$

Salem and Zygmund proved that $\sqrt{n \log n}$ is the right order of magnitude.
This was settled by Halász, who proved this is true with $C = 1$.
-/
@[category research solved, AMS 42 60]
theorem erdos_523 : answer(True) ↔
    ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
      {ε : ℕ → Ω → ℝ},
    (∀ k, IsRademacher μ (ε k)) → iIndepFun ε μ →
      ∃ C : ℝ, 0 < C ∧
      ∀ᵐ ω ∂μ, Tendsto
        (fun n => supNormCircle (fun k => ε k ω) n /
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
        atTop (nhds C) := by
  sorry

end Erdos523
