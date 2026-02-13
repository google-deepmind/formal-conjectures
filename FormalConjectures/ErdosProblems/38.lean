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
# Erdős Problem 38

*Reference:* [erdosproblems.com/38](https://www.erdosproblems.com/38)
-/

open Classical Set Pointwise

namespace Erdos38

/--
Does there exist $B \subset \mathbb{N}$ which is not an additive basis,
but is such that for every set $A \subseteq \mathbb{N}$ of Schnirelmann density $\alpha$
and every $N$ there exists $b \in B$ such that
\[
  \lvert (A \cup (A+b)) \cap \{1, \ldots, N\} \rvert \geq (\alpha + f(\alpha)) N
\]
where $f(\alpha) > 0$ for $0 < \alpha < 1$?
-/
@[category research open, AMS 11]
theorem erdos_38 : answer(sorry) ↔
    ∃ B : Set ℕ, ¬ B.IsAddBasis ∧ ∃ f : ℝ → ℝ, (∀ α, 0 < α → α < 1 → f α > 0) ∧
      ∀ (A : Set ℕ) (N : ℕ),
        let α := schnirelmannDensity A
        ∃ b ∈ B, (Ioc 0 N ∩ (A ∪ (A + {b}))).ncard ≥ (α + f α) * N := by
  sorry

end Erdos38
