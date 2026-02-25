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
# Erdős Problem 194

*References:*
- [erdosproblems.com/194](https://www.erdosproblems.com/194)
- [ABJ11] Ardal, H. and Brown, T. and Jungić, V., Chaotic orderings of the rationals and reals. Amer. Math. Monthly (2011), 921-925.
-/

namespace Erdos194

/--
Let $k\geq 3$. Must any ordering of $\mathbb{R}$ contain a monotone $k$-term arithmetic progression,
that is, some $x_1 <\cdots < x_k$ which forms an increasing or decreasing $k$-term arithmetic
progression?

The answer is no, even for $k=3$, as shown by Ardal, Brown, and Jungić [ABJ11].
-/
@[category research solved, AMS 5]
theorem erdos_194 :
  answer(False) ↔ ∀ k ≥ 3, ∀ r : ℝ → ℝ → Prop, IsStrictTotalOrder ℝ r →
    ∃ s : List ℝ, s.IsAPOfLength k ∧ (s.Pairwise r ∨ s.Pairwise (flip r)) := by
  sorry

end Erdos194
