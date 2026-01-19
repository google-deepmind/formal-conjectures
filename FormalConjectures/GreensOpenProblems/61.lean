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
# Ben Green's Open Problem 61

*Reference:* [Ben Green's Open Problem 61](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.8 Problem 61)

This problem was originally considered by Erdős and Newman.
-/

open scoped Pointwise
open Filter

namespace Green61
-- TODO(Paul-Lez): add the other two results
/--
Suppose that $A + A$ contains the first $n$ squares. Is $|A| \geq n^{1 - o(1)}$?

It is known that necessarily $|A| \geq n^{2/3 - o(1)}$, whilst in the other direction there do
exist such $A$ with $|A| \ll_C n / \log^C n$ for any $C$.
-/
@[category research open, AMS 11]
theorem green_61 :
    answer(sorry) ↔
      ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
        ∀ n ≥ 1, ∀ (A : Finset ℕ),
          (Finset.Icc 1 n).image (· ^ 2) ⊆ A + A →
            (n : ℝ) ^ (1 - f n) ≤ A.card := by
  sorry

end Green61
