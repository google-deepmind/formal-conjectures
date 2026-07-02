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

*References:*
- [erdosproblems.com/1174](https://www.erdosproblems.com/1174)
- [Va99] Vaughan, J.E. *Open problems in topology II*, problem 7.91 (1999).
-/

open Cardinal
open scoped Cardinal

namespace Erdos1174

/--
**Erdős Problem 1174, part (i)** [Va99, 7.91]. A problem of Erdős and Hajnal:
does there exist a graph $G$ with no $K_4$ such that every edge colouring of $G$
with countably many colours contains a monochromatic $K_3$?

For simplicity the colourings are given on all unordered pairs $\operatorname{Sym}_2(V)$;
only the values on the edges of $G$ matter, since a monochromatic triangle is witnessed by
edges alone.

Shelah proved that a graph with this property can consistently exist, so the
problem is not disprovable in ZFC; whether such a graph exists outright remains open.
-/
@[category research open, AMS 3 5]
theorem erdos_1174.parts.i : answer(sorry) ↔
    ∃ (V : Type) (G : SimpleGraph V), G.CliqueFree 4 ∧
      ∀ c : Sym2 V → ℕ, ∃ x y z : V,
        G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
        c s(x, y) = c s(y, z) ∧ c s(y, z) = c s(x, z) := by
  sorry

/--
**Erdős Problem 1174, part (ii)** [Va99, 7.91]. A problem of Erdős and Hajnal:
does there exist a graph $G$ with no $K_{\aleph_1}$ (that is, every clique of $G$
is countable) such that every edge colouring of $G$ with countably many colours
contains a monochromatic $K_{\aleph_0}$ (an infinite clique all of whose edges
receive the same colour)?

For simplicity the colourings are given on all unordered pairs $\operatorname{Sym}_2(V)$;
only the values on the edges of $G$ matter.

Shelah proved that a graph with this property can consistently exist, so the
problem is not disprovable in ZFC; whether such a graph exists outright remains open.
-/
@[category research open, AMS 3 5]
theorem erdos_1174.parts.ii : answer(sorry) ↔
    ∃ (V : Type) (G : SimpleGraph V),
      (∀ S : Set V, G.IsClique S → #S ≤ ℵ₀) ∧
      ∀ c : Sym2 V → ℕ, ∃ S : Set V, G.IsClique S ∧ S.Infinite ∧
        ∃ k : ℕ, ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c s(x, y) = k := by
  sorry

/-
**Shelah's consistency result.** Shelah proved that a graph with either property —
a $K_4$-free graph forcing a monochromatic $K_3$ in every countable edge colouring,
or a $K_{\aleph_1}$-free graph forcing a monochromatic $K_{\aleph_0}$ — can
*consistently* exist (i.e. in some model of ZFC). Hence neither question above can
be answered negatively in ZFC: the problem is "not disprovable". Formalizing the
consistency statement itself is out of scope here, since it cannot be stated in
plain ZFC (cf. the prose remark on Larson's MA result in Erdős Problem 601).
-/

/- ### Sanity checks -/

/-- The complete graph on $\mathbb{N}$ is *not* $K_4$-free, so it is not a candidate
for part (i). -/
@[category test, AMS 5]
theorem top_not_cliqueFree_four : ¬ (⊤ : SimpleGraph ℕ).CliqueFree 4 :=
  SimpleGraph.not_cliqueFree_of_top_embedding
    ⟨Fin.valEmbedding, by simp [Fin.val_injective.ne_iff]⟩

/-- The empty graph on $\mathbb{N}$ is trivially $K_4$-free but fails the colouring
property of part (i): it has no triangles at all, so the $K_4$-free condition alone
is not enough. -/
@[category test, AMS 5]
theorem bot_fails_colouring_property :
    ¬ ∀ c : Sym2 ℕ → ℕ, ∃ x y z : ℕ,
        (⊥ : SimpleGraph ℕ).Adj x y ∧ (⊥ : SimpleGraph ℕ).Adj y z ∧
        (⊥ : SimpleGraph ℕ).Adj x z ∧
        c s(x, y) = c s(y, z) ∧ c s(y, z) = c s(x, z) := by
  simp

end Erdos1174
