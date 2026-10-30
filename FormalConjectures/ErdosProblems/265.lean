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
# Erdős Problem 265

*Reference:* [erdosproblems.com/265](https://www.erdosproblems.com/265)
-/

@[expose] public section

namespace Erdos265

open Filter Topology

/--
Let $2 \leq a_0 < a_1 < \cdots$ be integers such that $\sum \frac{1}{a_n}$ and
$\sum \frac{1}{a_n - 1}$ are both rational. Is it necessary that $a_n^{1/2^n} \to 1$?
-/
@[category research open, AMS 11]
theorem erdos_265 : answer(sorry) ↔
    ∀ a : ℕ → ℕ, StrictMono a → 2 ≤ a 0 →
      (∃ q : ℚ, HasSum (fun n ↦ (1 : ℝ) / a n) q) →
      (∃ r : ℚ, HasSum (fun n ↦ (1 : ℝ) / (a n - 1)) r) →
      Tendsto (fun n ↦ (a n : ℝ) ^ (1 / (2 : ℝ) ^ n)) atTop (𝓝 1) := by
  sorry

end Erdos265
