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
# Erdős Problem 1174

*Reference:* [erdosproblems.com/1174](https://www.erdosproblems.com/1174)

A problem of Erdős and Hajnal on graph colourings and cliques.
Shelah proved that a graph with either property can consistently exist.

[Va99] Vardi, I. (ed.), *Problems from the Erdős problem collection*, §7.91 (1999).
-/

open Cardinal SimpleGraph

namespace Erdos1174

/--
Erdős Problem 1174, Part 1 [Va99, §7.91]:

Does there exist a graph $G$ with no $K_4$ (no 4-clique) such that for every
edge colouring of $G$ with countably many colours ($\mathbb{N}$), some monochromatic $K_3$
(a 3-clique whose three edges all receive the same colour) exists in $G$?

This is an open problem of Erdős and Hajnal. Shelah proved that such a graph
can consistently exist (i.e., its existence is consistent with ZFC).
-/
@[category research open, AMS 3 5]
theorem erdos_1174 : answer(sorry) ↔
    ∃ (V : Type) (G : SimpleGraph V),
      (∀ S : Finset V, ¬G.IsNClique 4 S) ∧
      ∀ (col : V → V → ℕ), (∀ u v : V, col u v = col v u) →
        ∃ (S : Finset V) (c : ℕ), G.IsNClique 3 S ∧
          ∀ u ∈ S, ∀ v ∈ S, u ≠ v → col u v = c := by
  sorry

/--
Erdős Problem 1174, Part 2 [Va99, §7.91]:

Does there exist a graph $G$ with no $K_{\aleph_1}$ (no clique of cardinality
$\geq \aleph_1$) such that for every edge colouring of $G$ with countably many colours
($\mathbb{N}$), some monochromatic $K_{\aleph_0}$ exists — that is, a clique of cardinality
$\geq \aleph_0$ whose edges all receive the same colour?

This is an open problem of Erdős and Hajnal. Shelah proved that such a graph
can consistently exist (i.e., its existence is consistent with ZFC).
-/
@[category research open, AMS 3 5]
theorem erdos_1174.variants.infinite_clique : answer(sorry) ↔
    ∃ (V : Type) (G : SimpleGraph V),
      (¬∃ S : Set V, aleph 1 ≤ Cardinal.mk ↥S ∧ G.IsClique S) ∧
      ∀ (col : V → V → ℕ), (∀ u v : V, col u v = col v u) →
        ∃ (S : Set V) (c : ℕ), aleph 0 ≤ Cardinal.mk ↥S ∧ G.IsClique S ∧
          ∀ u ∈ S, ∀ v ∈ S, u ≠ v → col u v = c := by
  sorry

end Erdos1174
