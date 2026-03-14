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
# Erdős Problem 347

*Reference:* [erdosproblems.com/347](https://www.erdosproblems.com/347)
-/

open Filter Set Topology

namespace Erdos347

/--
The set of subset sums of a set `A ⊆ ℕ`.
-/
local notation "𝓟" A => subsetSums A

/--
Is there a sequence $A=\{a_1\leq a_2\leq \cdots\}$ of integers with
\[\lim \frac{a_{n+1}}{a_n}=2\]
such that
\[P(A')= \left\{\sum_{n\in B}n : B\subseteq A'\textrm{ finite }\right\}\]
has density $1$ for every cofinite subsequence $A'$ of $A$?

This has been solved in the affirmative by ebarschkis in the comments (based on idea of Tao and
van Doorn, also in the comments).

Thos was formalized in Lean by Barschkis using Aristotle.
-/
@[category research formally solved using lean4 at
"https://github.com/ebarschkis/ErdosProblem/blob/main/Problem347/Formalization.lean", AMS 11]
theorem erdos_347 :
    answer(True) ↔ ∃ a : ℕ → ℕ, (Monotone a) ∧
      (Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ)) atTop (𝓝 2)) ∧
      (∀ ι : ℕ → ℕ, (range ι)ᶜ.Finite → HasDensity (𝓟 (range (a ∘ ι))) 1) := by
  sorry

end Erdos347
