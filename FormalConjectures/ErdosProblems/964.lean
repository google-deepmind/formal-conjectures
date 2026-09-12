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
# Erdős Problem 964

*Reference:* [erdosproblems.com/964](https://www.erdosproblems.com/964)
-/

open Set Topology

namespace Erdos964

/-- The set of ratios $\tau(n+1)/\tau(n)$ for $n\geq 1$. -/
noncomputable def divisorRatioSet : Set ℝ :=
  { (n.succ.divisors.card : ℝ) / n.divisors.card | (n : ℕ) (_ : 0 < n) }

/--
Let $\tau(n)$ count the number of divisors of $n$. Is the sequence
$$
\frac{\tau(n+1)}{\tau(n)}
$$
everywhere dense in $(0,\infty)$?
-/
@[category research open, AMS 11]
theorem erdos_964 :
    answer(sorry) ↔ Dense divisorRatioSet := by
  sorry

end Erdos964
