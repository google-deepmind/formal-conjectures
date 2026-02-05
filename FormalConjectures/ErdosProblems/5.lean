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

open Real Filter Function Set
open scoped Topology

namespace erdos_5

/--
There exists a strictly increasing sequence of indices (n_i)
such that the limit of $(p_{n_i+1} - p_{n_i}) / log p_{n_i}$ equals $\infty$,
where $p_k$ denotes the k-th prime number.

**Note:**
This definition is equivalent to $(p_{n_i+1} - p_{n_i}) / log n_i$
Since $p_n \sim n \log n$, then $\log n \sim \log p_n$
-/
@[category research solved, AMS 11]
theorem infinite_case :
    ∃ p : ℕ → ℕ, StrictMono p ∧ (∀ n : ℕ, (p n).Prime) ∧
    Tendsto (fun i ↦ (p (i+1) - p i) / log (p i)) atTop atTop := by
  sorry

/--
**The set of limit points of normalized prime gaps**
-/
def limit_points : Set ℝ :=
    {x : ℝ | ∃ p : ℕ → ℕ, StrictMono p ∧ (∀ n : ℕ, (p n).Prime) ∧
    Tendsto (fun i ↦ (p (i+1)  - p i) / log (p i)) atTop (𝓝 x) }

/--
For every nonnegative real number x, there exists a strictly increasing sequence of indices (n_i)
such that the limit of $(p_{n_i+1} - p_{n_i}) / log n_i$ equals $x$,
where $p_k$ denotes the k-th prime number.
-/
@[category research open, AMS 11]
theorem finite_case :
    {x : ℝ | 0 ≤ x} = limit_points := by
  sorry

/--
`limit_points` is everywhere dense.
-/
@[category research open, AMS 11]
theorem everywhere_dense :
    {x : ℝ | 0 ≤ x} = closure limit_points := by
  sorry

/--
At least 1/3 of positive real numbers are in the set of `limit_points` ($S$).
More precisely, the Lebesque measure of $S ∩ [0, c]$ is at least $c/3$.

[Me20] Merikoski, J. (2020) Limit points of normalized prime gaps.
-/
@[category research solved, AMS 11]
theorem contains_at_least_1_3 (c : ℝ) (hc : 0 ≤ c) :
    MeasureTheory.volume (limit_points ∩ Icc 0 c) > ENNReal.ofReal (c / 3) := by
  sorry

/--
There exists some constant $c$ such that $[0,c] \subset S$, where $S$ is `limit_points`.

[Pi16] Pintz, J. (2016) Polignac Numbers, Conjectures of Erdős on Gaps between
Primes, Arithmetic Progressions in Primes, and the Bounded Gap Conjecture.
-/
@[category research solved, AMS 11]
theorem contains_interval :
    ∃ (c : ℝ) (hc : 0 < c), {x : ℝ | 0 ≤ x ∧ x ≤ c} ⊆ limit_points := by
  sorry

end erdos_5
