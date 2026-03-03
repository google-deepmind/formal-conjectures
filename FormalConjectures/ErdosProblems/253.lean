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
# Erdős Problem 253

*Reference:* [erdosproblems.com/253](https://www.erdosproblems.com/253)
-/

namespace Erdos253

open scoped Topology

/-- The predicate that `a : ℕ → ℕ` is a strictly monotone sequence such that every infinite
arithmetic progression contains infinitely many integers that are the sum of distinct $a_i$s. -/
@[inline]
def RepresentsAPs (a : ℕ → ℕ) : Prop :=
    StrictMono a ∧ ∀ l, l.IsAPOfLength ⊤ → (subsetSums (Set.range a) ∩ l).Infinite

/--
Let $a_1 < a_2 < \dotsc$ be an infinite sequence of positive integers such that
$\frac{a_{i+1}}{a_i} \to 1$. If every arithmetic progression contains infinitely many
integers which are the sum of distinct $a_i$ then every sufficiently large integer is
the sum of distinct $a_i$.
-/
@[category research formally solved using formal_conjectures at "https://www.erdosproblems.com/253", AMS 11]
theorem erdos_253 : ¬ ∀ a : ℕ → ℕ, 0 < a 0 →
    RepresentsAPs a → (Filter.atTop.Tendsto (fun n ↦ (a <| n + 1 : ℝ) / a n) (𝓝 1)) →
      subsetSums (Set.range a) ∈ Filter.cofinite := by
  sorry

end Erdos253
