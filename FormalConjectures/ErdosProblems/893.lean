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
# Erdős Problem 893

*References:*
- [erdosproblems.com/893](https://www.erdosproblems.com/893)
- [KoLu25] V. Kovač and F. Luca, On the number of divisors of Mersenne numbers. arXiv:2506.04883 (2025).
-/

open Filter Finset
open scoped ArithmeticFunction.sigma

namespace Erdos893

/--
Definition of function $f(n) := \sum_{1\leq k\leq n}\tau(2^k-1)$.
Here $\tau$ is the divisor counting function, which is `σ 0` in mathlib.
-/
def f (n : ℕ) : ℕ :=  ∑ k ∈ Finset.Icc 1 n, σ 0 (2^k - 1)

/--
Does the limit $\lim_{n\to\infty} \frac{f(2n)}{f(n)}$ tend to infinity?

(Other finite limits have been ruled out by [KoLu25], see below)
-/
@[category research open, AMS 5]
theorem erdos_893 :
    answer(sorry) ↔ Tendsto (fun n : ℕ => (f (2 * n) : ℝ) / (f n : ℝ)) atTop atTop := by
  sorry


/--
Kovač and Luca [KoLu25] (building on a heuristic independently found by
Cambie (personal communication)) have shown that there is no finite limit, in that
$\lim_{n\to\infty} \frac{f(2n)}{f(n)}$ is unbounded.
-/
@[category research solved, AMS 5]
theorem erdos_893.variants.unbounded :
   ¬ BddAbove (Set.range fun n : ℕ => (f (2 * n) : ℝ) / f n) := by
  sorry


end Erdos893
