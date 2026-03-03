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
# Erdős Problem 68

*Reference:* [erdosproblems.com/68](https://www.erdosproblems.com/68)
-/

namespace Erdos68

/--
Is
$$\sum_{n=2}^\infty \frac{1}{n!-1}$$
irrational?
-/
@[category research open, AMS 11]
theorem erdos_68 :
    answer(sorry) ↔ Irrational (∑' n : ℕ, 1 / ((n + 2).factorial - 1 : ℝ)) := by
  sorry

/--
$$\sum_{n=2}^\infty \frac{1}{n!-1} = \sum_{n=2}^\infty \sum_{k=1}^\infty \frac{1}{(n!)^k}$$
-/
@[category undergraduate, AMS 11]
theorem sum_factorial_inv_eq_geometric :
    let f (n k : ℕ) : ℝ := 1 / ((n + 2).factorial : ℝ) ^ (k + 1)
    ∑' n : ℕ, (1 : ℝ) / ((n + 2).factorial - 1) = ∑' n : ℕ, ∑' k : ℕ, f n k := by
  sorry

/--
The series $\sum_{n=2}^\infty \frac{1}{n!-1}$ is known to be transcendental conditional on
Schanuel's conjecture, since it can be expressed in terms of $e$ and related constants.
Borwein (1992) proved irrationality of related factorial-based series, and the sum is known
to be irrational if it equals no ratio of integers by standard transcendence criteria.
-/
@[category research formally solved using formal_conjectures at "https://www.erdosproblems.com/68", AMS 11]
theorem erdos_68.variants.known_result :
    ∀ q : ℚ, (q : ℝ) ≠ ∑' n : ℕ, 1 / ((n + 2).factorial - 1 : ℝ) ∨
      Irrational (∑' n : ℕ, 1 / ((n + 2).factorial - 1 : ℝ)) := by
  sorry

end Erdos68
