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
# Erdős Problem 994

*Reference:* [erdosproblems.com/994](https://www.erdosproblems.com/994)
-/

open Filter MeasureTheory Set Real
open scoped Topology

namespace Erdos994

/--
Let $E\subseteq (0,1)$ be a measurable subset with Lebesgue measure $\lambda(E)$. Is it true that,
for almost all $\alpha$,
$$
\lim_{n\to \infty}\frac{1}{n}\sum_{1\leq k\leq n}1_{\{k\alpha \}\in E}=\lambda(E)
$$
for all $E$?
-/
@[category research open, AMS 11 28]
theorem erdos_994 :
    answer(sorry) ↔
      ∀ᵐ α : ℝ,
        ∀ E : Set ℝ, MeasurableSet E → E ⊆ Ioo (0 : ℝ) 1 →
          Tendsto (fun n : ℕ ↦
            ({ k : ℕ | 1 ≤ k ∧ k ≤ n ∧ Int.fract ((k : ℝ) * α) ∈ E }.ncard : ℝ) / n)
            atTop (𝓝 (volume E).toReal) := by
  sorry

end Erdos994
