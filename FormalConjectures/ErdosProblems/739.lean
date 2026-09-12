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

universe u

/-!
# Erdős Problem 739

*Reference:* [erdosproblems.com/739](https://www.erdosproblems.com/739)
-/

open Cardinal SimpleGraph

namespace Erdos739

/--
The chromatic number of `G` as a cardinal: the least `κ` such that `G` admits a proper colouring
with a colour-set of cardinality `κ`.
-/
noncomputable def chromaticCard {V : Type u} (G : SimpleGraph V) : Cardinal.{u} :=
  sInf {κ : Cardinal.{u} | ∃ (C : Type u), Cardinal.mk C = κ ∧ Nonempty (G.Coloring C)}

/--
Let $\mathfrak{m}$ be an infinite cardinal and $G$ be a graph with chromatic number
$\mathfrak{m}$. Is it true that, for every infinite cardinal $\mathfrak{n}< \mathfrak{m}$,
there exists a subgraph of $G$ with chromatic number $\mathfrak{n}$?
-/
@[category research open, AMS 5]
theorem erdos_739 : answer(sorry) ↔
    ∀ {V : Type u} (G : SimpleGraph V) (m : Cardinal.{u}),
      ℵ₀ ≤ m → chromaticCard G = m →
      ∀ n : Cardinal.{u}, ℵ₀ ≤ n → n < m →
        ∃ s : G.Subgraph, chromaticCard s.coe = n := by
  sorry

end Erdos739
