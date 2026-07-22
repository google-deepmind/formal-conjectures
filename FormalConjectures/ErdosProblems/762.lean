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

import FormalConjecturesUtil

/-!
# Erdős Problem 762

*References:*
- [erdosproblems.com/762](https://www.erdosproblems.com/762)
- [EGS90] Erdős, Paul and Gimbel, John and Straight, H. Joseph, *Chromatic number versus
  cochromatic number in graphs with bounded clique number*. European J. Combin. (1990), 235-240.
- [St24b] R. Steiner, *On the difference between the chromatic and cochromatic number*.
  arXiv:2408.02400 (2024).
-/

namespace Erdos762

/--
The cochromatic number of $G$, denoted by $\zeta(G)$, is the minimum number of colours needed to
colour the vertices of $G$ such that each colour class induces either a complete graph or empty
graph.

Is it true that if $G$ has no $K_5$ and $\zeta(G)\geq 4$ then $\chi(G) \leq \zeta(G)+2$?

This has been disproved by Steiner [St24b], who constructed a graph $G$ with $\omega(G)=4$,
$\zeta(G)=4$, and $\chi(G)=7$.
-/
@[category research solved, AMS 5]
theorem erdos_762 : answer(False) ↔
    ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree 5 → 4 ≤ G.cochromaticNumber →
        G.chromaticNumber ≤ G.cochromaticNumber + 2 := by
  sorry

/--
A conjecture of Erdős, Gimbel, and Straight [EGS90], who proved that for every $n>2$ there exists
some $f(n)$ such that if $G$ contains no clique on $n$ vertices then $\chi(G)\leq \zeta(G)+f(n)$.
-/
@[category research solved, AMS 5]
theorem erdos_762.variants.bounded_clique_number (n : ℕ) (hn : 2 < n) :
    ∃ f : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f := by
  sorry

/--
This has been disproved by Steiner [St24b], who constructed a graph $G$ with $\omega(G)=4$,
$\zeta(G)=4$, and $\chi(G)=7$.
-/
@[category research solved, AMS 5]
theorem erdos_762.variants.steiner :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.cliqueNum = 4 ∧ G.cochromaticNumber = 4 ∧ G.chromaticNumber = 7 := by
  sorry

end Erdos762
