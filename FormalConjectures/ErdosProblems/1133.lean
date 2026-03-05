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
# Erdős Problem 1133

*Reference:* [erdosproblems.com/1133](https://www.erdosproblems.com/1133)

Erdős proved that, for any $C > 0$, there exists $\varepsilon > 0$ such that if $n$ is sufficiently
large and $m = \lfloor(1+\varepsilon)n\rfloor$ then for any $x_1, \ldots, x_m \in [-1,1]$ there is
a polynomial $P$ of degree $n$ such that $|P(x_i)| \le 1$ for $1 \le i \le m$ and
$\max_{x \in [-1,1]} |P(x)| > C$.
The conjectured statement would also imply this, but Erdős said he could not even prove
it for $m = n$.
-/

open Polynomial Finset Set

namespace Erdos1133

/--
Erdős Problem 1133:
Let $C > 0$. There exists $\varepsilon > 0$ such that for sufficiently large $n$, for any
$x_1, \ldots, x_n \in [-1,1]$ there exist $y_1, \ldots, y_n \in [-1,1]$ such that any polynomial
$P$ of degree $< (1+\varepsilon)n$ that agrees with $y_i$ at $x_i$ for at least $(1-\varepsilon)n$
indices $i$ must satisfy $\max_{x \in [-1,1]} |P(x)| > C$.
-/
@[category research open, AMS 41]
theorem erdos_1133 :
    ∀ C : ℝ, C > 0 →
    ∃ ε : ℝ, ε > 0 ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ x : Fin n → ℝ, (∀ i, x i ∈ Icc (-1 : ℝ) 1) →
    ∃ y : Fin n → ℝ, (∀ i, y i ∈ Icc (-1 : ℝ) 1) ∧
    ∀ P : Polynomial ℝ, (P.natDegree : ℝ) < (1 + ε) * n →
    ((univ.filter (fun i : Fin n => P.eval (x i) = y i)).card : ℝ) ≥ (1 - ε) * n →
    ∃ t ∈ Icc (-1 : ℝ) 1, |P.eval t| > C := by
  sorry

end Erdos1133
