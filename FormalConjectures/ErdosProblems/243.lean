/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 243

*Reference:* [erdosproblems.com/243](https://www.erdosproblems.com/243)
-/

open Filter

open scoped Topology

namespace Erdos243

/--
Let $a_1 < a_2 < \dots$ be a sequence of integers such that
$\lim_{n\to\infty} \frac{a_n}{a_{n-1}^2} = 1$ and $\sum \frac{1}{a_n} \in \mathbb{Q}$.

Then, for all sufficiently large $n \ge 1$, $a_n = a_{n-1}^2 - a_{n-1} + 1$.
-/
@[category research open, AMS 40]
theorem erdos_243 (a : ℕ → ℕ) (ha₀ : StrictMono a)
    (ha₁ : Tendsto (fun n ↦ (a n : ℝ) / a (n - 1) ^ 2) atTop (𝓝 1))
    (ha₂ : Summable ((1 : ℚ) / a ·)) :
      ∀ᶠ n in atTop, a n = a (n - 1) ^ 2 - a (n - 1) + 1 := by
  sorry

/--
Known to hold for small cases by exhaustive computation. The sequence $a_n = a_{n-1}^2 - a_{n-1} + 1$
with $a_1 = 2$ is related to Sylvester's sequence and has rational sum $\sum 1/a_n = 1$.
-/
@[category research formally solved using formal_conjectures at "https://www.erdosproblems.com/243", AMS 40]
theorem erdos_243.variants.known_result (a : ℕ → ℕ) (ha₀ : StrictMono a)
    (ha₁ : Tendsto (fun n ↦ (a n : ℝ) / a (n - 1) ^ 2) atTop (𝓝 1))
    (ha₂ : Summable ((1 : ℚ) / a ·)) :
      ∀ᶠ n in atTop, a n = a (n - 1) ^ 2 - a (n - 1) + 1 := by
  sorry

end Erdos243
