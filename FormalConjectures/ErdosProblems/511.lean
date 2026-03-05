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
# Erdős Problem 511

*Reference:* [erdosproblems.com/511](https://www.erdosproblems.com/511)

Let $f(z) \in \mathbb{C}[z]$ be a monic polynomial of degree $n$. Is it true that,
for every $c > 1$, the set $\{z \in \mathbb{C} : |f(z)| < 1\}$ has at most $O_c(1)$
many connected components of diameter $> c$ (where the implied constant is
independent of $n$)?

Disproved by Pommerenke, who showed that for any $0 < d < 4$ and $k \geq 1$,
there exist monic polynomials $f \in \mathbb{C}[x]$ such that
$\{z : |f(z)| \leq 1\}$ has at least $k$ connected components of diameter $\geq d$.
-/

open Polynomial Set

namespace Erdos511

/-- Erdős Problem 511: Is it true that for every $c > 1$, there exists a bound $M$
(independent of the degree) such that for any monic polynomial $f \in \mathbb{C}[z]$,
the sublevel set $\{z \in \mathbb{C} : \|f(z)\| < 1\}$ has at most $M$ connected
components of diameter $> c$?

Disproved by Pommerenke. -/
@[category research solved, AMS 30]
theorem erdos_511 : answer(False) ↔
    ∀ c : ℝ, c > 1 →
      ∃ M : ℕ, ∀ (f : Polynomial ℂ),
        f.Monic →
          ∀ (k : ℕ) (C : Fin k → Set ℂ),
            (∀ i, (C i).Nonempty) →
            (∀ i, C i ⊆ {z : ℂ | ‖Polynomial.eval z f‖ < 1}) →
            (∀ i, IsPreconnected (C i)) →
            (∀ i, Metric.diam (C i) > c) →
            (∀ i j, i ≠ j → Disjoint (C i) (C j)) →
            k ≤ M := by
  sorry

end Erdos511
