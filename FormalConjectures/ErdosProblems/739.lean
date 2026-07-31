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
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Erdős Problem 739

*Reference:* [erdosproblems.com/739](https://www.erdosproblems.com/739)

Let $\mathfrak{m}$ be an infinite cardinal and $G$ be a graph with chromatic number $\mathfrak{m}$.
Is it true that, for every infinite cardinal $\mathfrak{n}< \mathfrak{m}$,
there exists a subgraph of $G$ with chromatic number $\mathfrak{n}$?
-/

namespace Erdos739

open Cardinal

/--
Abstract notion of a graph. In practice one would use `SimpleGraph` from Mathlib,
but here we keep the definition minimal for the conjecture.
-/
class Graph (V : Type*) where
  -- adjacency relation, etc. (not needed for the statement)
  dummy : Unit

/--
The chromatic number of a graph as a cardinal. This is a placeholder;
the actual definition can be found in `Mathlib.Combinatorics.SimpleGraph.ChromaticNumber`.
-/
noncomputable def chromaticNumber (V : Type*) [Graph V] : Cardinal := sorry

/--
The predicate that one graph is a subgraph of another. Again, a placeholder.
-/
def isSubgraph {V : Type*} [Graph V] (H G : Type*) [Graph H] [Graph G] : Prop := sorry

/--
Erdős Problem 739 (conjecture):
For any infinite cardinal `m`, any graph `G` with chromatic number `m`,
and any infinite cardinal `n < m`, there exists a subgraph `H` of `G` with chromatic number `n`.
-/
@[category research open, AMS 52]
theorem erdos_739 (m n : Cardinal) [h_m : m.Infinite] [h_n : n.Infinite]
    (G : Type*) [Graph G] (hG : chromaticNumber G = m) (hn : n < m) :
    ∃ (H : Type*) [Graph H], isSubgraph H G ∧ chromaticNumber H = n := by
  sorry

end Erdos739
