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
import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 144

*Reference:* [erdosproblems.com/144](https://www.erdosproblems.com/144)

[Er61, Er77c, Er79, Er79e, ErGr80, Er81h, Er82e, Er85e, Er97c, Er98] Erdős, P., various papers.

[ErHa79] Erdős, P. and Hall, R. R., *The propinquity of divisors*, Bull. London Math. Soc.
(1979), 304–307.

[MaTe84] Maier, H. and Tenenbaum, G., *On the set of divisors of an integer*, Invent. Math. **76**
(1984), 121–128.

*Related problems:* [449](https://www.erdosproblems.com/449),
[884](https://www.erdosproblems.com/884)

*OEIS:* [A005279](https://oeis.org/A005279)
-/

namespace Erdos144

/-- A positive integer $n$ has two divisors $d_1, d_2$ with $d_1 < d_2 < 2d_1$. -/
def HasCloseDivisorPair (n : ℕ) : Prop :=
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
    {n : ℕ | HasCloseDivisorPair n}.HasDensity 1 := by
  sorry

/--
Erdős Problem 144, generalized [MaTe84]:
For any constant $c > 1$, the density of integers which have two divisors
$d_1, d_2$ such that $d_1 < d_2 < c \cdot d_1$ exists and is equal to $1$.

This is the stronger result proved by Maier and Tenenbaum, generalizing the
original problem where $c = 2$.
-/
@[category research solved, AMS 11]
theorem erdos_144_generalized (c : ℝ) (hc : 1 < c) :
    {n : ℕ | ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧ (d₂ : ℝ) < c * d₁}.HasDensity 1 := by
  sorry

end Erdos144
