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

Disproved by Pommerenke [Po61], who showed that for any $0 < d < 4$ and $k \geq 1$,
there exist monic polynomials $f \in \mathbb{C}[x]$ such that
$\{z : |f(z)| \leq 1\}$ has at least $k$ connected components of diameter $\geq d$.
Huang [Hu25] independently obtained the same result.

Pólya [Po28] proved that no connected component of $\{z : |f(z)| \leq 1\}$ can have
diameter exceeding $4$, so the conjecture is vacuously true for $c \geq 4$.

[EHP58] Erdős, P., Herzog, F., and Piranian, G., *Metric properties of polynomials*,
J. Analyse Math. 6 (1958), 125–148.

[Er61] Erdős, P., *Some unsolved problems*, Magyar Tud. Akad. Mat. Kutató Int. Közl.
6 (1961), 221–254.

[Ha74] Hayman, W. K., *Research problems in function theory: new problems*, (1974),
155–180.

[Po28] Pólya, G., *Beitrag zur Verallgemeinerung des Verzerrungssatzes auf mehrfach
zusammenhängende Gebiete*, S.-B. Preuss. Akad. Wiss. (1928), 228–232, 280–282.

[Po61] Pommerenke, Ch., *On metric properties of complex polynomials*, Michigan Math. J.
8 (1961), 97–115.

[Hu25] Huang, L., *Many lemniscates with large diameter*, arXiv:2509.11597, 2025.
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

/-- Pólya's theorem [Po28]: Every connected component of the sublevel set
$\{z \in \mathbb{C} : \|f(z)\| \leq 1\}$ for a monic polynomial $f$ has diameter at most $4$.
This provides the complementary upper bound that explains why Problem 511 concerns $c > 1$:
for $c \geq 4$, the conjecture is vacuously true. -/
@[category research solved, AMS 30]
theorem erdos_511_polya_upper :
    ∀ (f : Polynomial ℂ), f.Monic →
      ∀ (S : Set ℂ), S ⊆ {z : ℂ | ‖Polynomial.eval z f‖ ≤ 1} →
        IsPreconnected S →
          Metric.diam S ≤ 4 := by
  sorry

end Erdos511
