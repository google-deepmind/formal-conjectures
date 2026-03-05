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
# Erdős Problem 450

*Reference:* [erdosproblems.com/450](https://www.erdosproblems.com/450)

How large must $y = y(\varepsilon, n)$ be such that the number of integers in $(x, x+y)$ with a
divisor in $(n, 2n)$ is at most $\varepsilon \cdot y$?

The intended quantifier on $x$ is not entirely clear from the original source. We formalize
the "for all $x$" interpretation: for every $\varepsilon > 0$ and $n \geq 1$, there exists $y$
such that for all $x$, the count of integers in $(x, x+y)$ with a divisor in $(n, 2n)$ is at most
$\varepsilon \cdot y$.

Cambie observed that the "for all $x$" version fails when
$\varepsilon \cdot (\log n)^{\delta} \cdot (\log \log n)^{3/2} \to \infty$ (using results of
Ford [Fo08]), so this formalization may require additional conditions on $\varepsilon$ and $n$.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[Fo08] Ford, K., *The distribution of integers with a divisor in a given interval*. Annals of
Mathematics (2008).
-/

open Finset Classical

namespace Erdos450

/-- Count of integers in the open interval $(x, x + y)$ having at least one divisor
in the open interval $(n, 2n)$. -/
noncomputable def countWithDivisorInRange (x y n : ℕ) : ℕ :=
  ((Finset.Ioo x (x + y)).filter (fun m =>
    ∃ d ∈ Finset.Ioo n (2 * n), d ∣ m)).card

/--
Erdős Problem 450 [ErGr80, p.89]:

For every $\varepsilon > 0$ and $n \geq 1$, there exists $y$ such that for all $x$, the number of
integers in $(x, x + y)$ with a divisor in $(n, 2n)$ is at most $\varepsilon \cdot y$.
-/
@[category research open, AMS 11]
theorem erdos_450 (ε : ℝ) (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n) :
    ∃ y : ℕ, 0 < y ∧ ∀ x : ℕ,
      (countWithDivisorInRange x y n : ℝ) ≤ ε * (y : ℝ) := by
  sorry

end Erdos450
