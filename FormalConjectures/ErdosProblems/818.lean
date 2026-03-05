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
# Erdős Problem 818

*Reference:* [erdosproblems.com/818](https://www.erdosproblems.com/818)

Let $A$ be a finite set of integers such that $|A+A| \ll |A|$. Is it true that
$$|AA| \gg \frac{|A|^2}{(\log |A|)^C}$$
for some constant $C > 0$?

A problem of Erdős [Er91]. This was proved by Solymosi [So09d], in the strong form
$|AA| \gg |A|^2 / \log |A|$.

[Er91] Erdős, P., _Some of my favourite problems in number theory, combinatorics, and geometry_. Resenhas do Instituto de Matemática e Estatística da Universidade de São Paulo (1991).

[So09d] Solymosi, J., _Bounding multiplicative energy by the sumset_. Advances in Mathematics (2009).
-/

open Finset Real

open scoped Pointwise

namespace Erdos818

/--
**Erdős Problem 818** (proved by Solymosi [So09d]):

There exists a constant $C > 0$ such that for every $K > 0$, there exists $c > 0$
such that for every finite set $A$ of integers with $|A + A| \leq K \cdot |A|$,
we have $|A \cdot A| \geq c \cdot |A|^2 / (\log |A|)^C$.
-/
@[category research solved, AMS 5 11]
theorem erdos_818 :
    answer(True) ↔
    ∃ C : ℝ, C > 0 ∧
    ∀ K : ℝ, K > 0 →
    ∃ c : ℝ, c > 0 ∧
    ∀ A : Finset ℤ, (A.card : ℝ) ≥ 2 →
    ((A + A).card : ℝ) ≤ K * A.card →
    ((A * A).card : ℝ) ≥ c * (A.card : ℝ) ^ 2 / (Real.log (A.card : ℝ)) ^ C := by
  sorry

end Erdos818
