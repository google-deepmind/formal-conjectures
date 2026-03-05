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
# Erdős Problem 144

*Reference:* [erdosproblems.com/144](https://www.erdosproblems.com/144)

[Er61, Er77c, Er79, Er79e, ErGr80, Er81h, Er82e, Er85e, Er97c, Er98] Erdős, P., various papers.

[MaTe84] Maier, H. and Tenenbaum, G., *On the set of divisors of an integer*, Invent. Math. 76
(1984), 121–128.
-/

open Filter

open scoped Topology

attribute [local instance] Classical.propDecidable

namespace Erdos144

/-- A positive integer $n$ has two divisors $d_1, d_2$ with $d_1 < d_2 < 2d_1$. -/
def HasCloseConsecutiveDivisors (n : ℕ) : Prop :=
  ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧ d₂ < 2 * d₁

/--
Erdős Problem 144 [Er61, Er77c, Er79, Er79e, ErGr80, Er81h, Er82e, Er85e, Er97c, Er98]:
The density of integers which have two divisors $d_1, d_2$ such that $d_1 < d_2 < 2d_1$
exists and is equal to $1$.

Formally, writing $A(N)$ for the number of integers $n$ with $1 \le n \le N$ which have
two divisors $d_1 < d_2 < 2d_1$, we have $A(N)/N \to 1$ as $N \to \infty$.

Proved by Maier and Tenenbaum [MaTe84].
-/
@[category research solved, AMS 11]
theorem erdos_144 :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter (fun n => HasCloseConsecutiveDivisors (n + 1))).card : ℝ) /
        (N : ℝ))
      atTop
      (𝓝 (1 : ℝ)) := by
  sorry

end Erdos144
