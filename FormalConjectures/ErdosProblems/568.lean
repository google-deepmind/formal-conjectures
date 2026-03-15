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
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Erdős Problem 568

*Reference:* [erdosproblems.com/568](https://www.erdosproblems.com/568)

A problem of Erdős, Faudree, Rousseau, and Schelp.

[EFRS93] Erdős, P., Faudree, R., Rousseau, C., and Schelp, R., _Ramsey size linear graphs_.
Combin. Probab. Comput. (1993), 389-399.
-/

namespace Erdos568

open SimpleGraph

/-- The Ramsey number $R(G, H)$: the minimum $N$ such that for any graph $F$
on $\operatorname{Fin} N$, either $G$ embeds in $F$ or $H$ embeds in the
complement of $F$. -/
noncomputable def ramseyNum {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) : ℕ :=
  sInf {N : ℕ | ∀ (F : SimpleGraph (Fin N)),
    G ⊑ F ∨ H ⊑ Fᶜ}

/--
Erdős Problem 568:

Let $G$ be a graph such that:
1. $R(G, T) = O(n)$ for every tree $T$ on $n$ vertices, and
2. $R(G, K_n) = O(n^2)$.

Is it true that for any graph $H$ with $m$ edges and no isolated vertices,
$R(G, H) = O(m)$?

In other words, is $G$ Ramsey size linear?

[EFRS93]
-/
@[category research open, AMS 5]
theorem erdos_568 : answer(sorry) ↔
    ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
    (∃ C₁ : ℕ, ∀ (n : ℕ) (T : SimpleGraph (Fin n)),
      T.IsTree → ramseyNum G T ≤ C₁ * n) →
    (∃ C₂ : ℕ, ∀ (n : ℕ),
      ramseyNum G (⊤ : SimpleGraph (Fin n)) ≤ C₂ * n ^ 2) →
    ∃ C : ℕ, ∀ (k : ℕ) (H : SimpleGraph (Fin k)),
      (∀ v : Fin k, ∃ w, H.Adj v w) →
      ramseyNum G H ≤ C * H.edgeSet.ncard := by
  sorry

end Erdos568
