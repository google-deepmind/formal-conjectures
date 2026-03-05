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
# Erdős Problem 821

*Reference:* [erdosproblems.com/821](https://www.erdosproblems.com/821)

Let $g(n)$ count the number of $m$ such that $\varphi(m) = n$. Is it true that,
for every $\varepsilon > 0$, there exist infinitely many $n$ such that
$g(n) > n^{1 - \varepsilon}$?

Pillai proved that $\limsup g(n) = \infty$ and Erdős [Er35b] proved that there
exists some constant $c > 0$ such that $g(n) > n^c$ for infinitely many $n$.
The best known bound is $g(n) > n^{0.71568\ldots}$ for infinitely many $n$,
obtained by Lichtman [Li22].
-/

namespace Erdos821

/-- The number of positive integers $m$ such that $\varphi(m) = n$. -/
noncomputable def totientPreimageCount (n : ℕ) : ℕ :=
  Nat.card {m : ℕ // 0 < m ∧ Nat.totient m = n}

/--
Erdős Problem 821 [Er74b]:

Is it true that for every $\varepsilon > 0$, there exist infinitely many $n$ such that
$g(n) > n^{1-\varepsilon}$, where $g(n)$ counts the number of $m$ with $\varphi(m) = n$?
-/
@[category research open, AMS 11]
theorem erdos_821 : answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 →
      Set.Infinite {n : ℕ | (totientPreimageCount n : ℝ) > (n : ℝ) ^ (1 - ε)} := by
  sorry

end Erdos821
