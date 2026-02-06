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
# Erdős Problem 1060

*Reference:* [erdosproblems.com/1060](https://www.erdosproblems.com/1060)
-/

open Asymptotics Finset Filter Real
open scoped ArithmeticFunction.sigma

namespace Erdos1060

/-- The conjecture is about the function $f(n)$ which counts the number of solutions to
$k\sigma(k)=n$, where $\sigma(k)$ is the sum of divisors of $k$. The first bound is that $f(n)$ grows slower
than any power of $n^(\frac{1}{\log\log n})$. The second bound is that $f(n)$ is at most a power of
$\log n$.
-/

@[category research open, AMS 11]
theorem erdos_1060.bound_one :
    ∃ h : ℕ → ℝ,
      h =o[atTop] (fun n ↦ 1 / log (log n)) ∧ ∀ᶠ n in atTop, #{k ≤ n | k * σ 1 k = n} ≤ (n : ℝ) ^ h n := by sorry

@[category research open, AMS 11]
theorem erdos_1060.bound_two :
    ∃ (C : ℝ), (fun n ↦ (#{k ≤ n | k * σ 1 k = n} : ℝ)) =O[atTop]
      (fun n ↦ log n ^ C) := by sorry

end Erdos1060
