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
# Erdős Problem 5

*Reference:* [erdosproblems.com/5](https://www.erdosproblems.com/5)
-/

open Real Filter Function
open scoped Topology

/--
For every nonnegative real number x, there exists a strictly increasing sequence of indices (n_i)
such that the limit of $(p_{n_{i+1}} - p_{n_i}) / log n_i$ equals $x$,
where $p_k$ denotes the k-th prime number.

Note: the condition `n 0 ≥ 2` ensures the logarithm is defined for all indices
-/
@[category research open, AMS 11]
theorem erdos_5.finite_case (x : ℝ) (hx : 0 ≤ x) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ n 0 ≥ 2 ∧
    Tendsto (fun i ↦ ((n (i+1)).nth Prime  - (n i).nth Prime : ℝ) / log (n i)) atTop (𝓝 x) := by
  sorry

/--
There exists a strictly increasing sequence of indices (n_i)
such that the limit of $(p_{n_{i+1}} - p_{n_i}) / log n_i$ equals $\infty$,
where $p_k$ denotes the k-th prime number.

Note: the condition `n 0 ≥ 2` ensures the logarithm is defined for all indices
-/
@[category research solved, AMS 11]
theorem erdos_5.infinite_case :
    ∃ n : ℕ → ℕ, StrictMono n ∧ n 0 ≥ 2 ∧
    Tendsto (fun i ↦ ((n (i+1)).nth Prime  - (n i).nth Prime : ℝ) / log (n i)) atTop atTop := by
  sorry
