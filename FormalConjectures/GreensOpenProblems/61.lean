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

open scoped Pointwise

/-!
# Ben Green's Open Problem 61

*Reference:* [Ben Green's Open Problem 61](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.8 Problem 61)
-/

open Filter

namespace Green61

/--
Suppose that $A + A$ contains the first $n$ squares. Is $|A| ≥ n^{1 - o(1)}$?

The best known results are from Erdős and Newman, showing that necessarily $|A| ≥ n^{2/3 - o(1)}$,
while in the other direction there exist such $A$ with $|A| ≪_C n / \log^C n$ for any $C$.
-/
@[category research open, AMS 11]
theorem green_61 :
    answer(sorry) ↔ ∃ o : ℕ → ℝ, Tendsto o atTop (𝓝 0) ∧
      ∀ n, ∀ (A : Finset ℕ),
        (∀ k ∈ Finset.Icc 1 n, k ^ 2 ∈ A + A) →
          (A.card : ℝ) ≥ n ^ (1 - o n) := by
  sorry

end Green61
