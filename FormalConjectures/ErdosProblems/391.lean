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
# Erdős Problem 391

Let $t(n)$ be the maximal value such that $n!$ can be written as a product
of $n$ positive integers, each at least $t(n)$. Erdős conjectured that
$t(n)/n \to 1/e$.

*Reference:* [erdosproblems.com/391](https://www.erdosproblems.com/391)
-/

open BigOperators Filter

namespace Erdos391

/--
A valid representation of $n!$ as a product of $n$ positive integers in
non-decreasing order.
-/
def IsFactorialRepr (n : ℕ) (f : Fin n → ℕ) : Prop :=
  (∀ i, 0 < f i) ∧ Monotone f ∧ ∏ i, f i = n.factorial

/--
$t(n)$ is the maximal value of the smallest factor in any representation of $n!$
as a product of $n$ positive integers in non-decreasing order.
-/
noncomputable def erdos391_t (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ f : Fin n → ℕ, IsFactorialRepr n f ∧ ∀ i, k ≤ f i}

/--
Let $t(n)$ be maximal such that $n! = a_1 \cdots a_n$ with
$t(n) = a_1 \leq \cdots \leq a_n$.
The limit of $t(n)/n$ as $n \to \infty$ equals $1/e$.
-/
@[category research solved, AMS 11]
theorem erdos_391 :
    Tendsto (fun n : ℕ => (erdos391_t n : ℝ) / (n : ℝ))
      atTop (nhds (1 / Real.exp 1)) := by
  sorry

/--
There exists a constant $c > 0$ such that $t(n)/n \leq 1/e - c/\log(n)$ for
infinitely many $n$.
-/
@[category research open, AMS 11]
theorem erdos_391.variants.rate_of_convergence :
    ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (erdos391_t n : ℝ) / (n : ℝ) ≤ 1 / Real.exp 1 - c / Real.log (n : ℝ) := by
  sorry

end Erdos391
