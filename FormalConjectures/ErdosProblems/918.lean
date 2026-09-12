/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 918

*References:*
- [erdosproblems.com/918](https://www.erdosproblems.com/918)
- [ErHa68b] Erdős, P. and Hajnal, A., On chromatic number of infinite graphs. (1968), 83--98.
- [Er69b] Erdős, P., Problems and results in chromatic graph theory. Proof Techniques in Graph Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
- [Bau84] Baumgartner, J. E., Generic graph construction. J. Symbolic Logic 49 (1984), 234--240.
- [FL88] Foreman, M. and Laver, R., Some downwards transfer properties for $\aleph_2$.
  Adv. in Math. 67 (1988), 230--238.
- [LHR19] Lambie-Hanson, C. and Rinot, A., Reflection on the coloring and chromatic numbers.
  Combinatorica 39 (2019), 165--214. [arXiv:1708.06929](https://arxiv.org/abs/1708.06929)
-/

universe u

open scoped Cardinal Ordinal

namespace Erdos918

-- Formalisation note: source material [ErHa68b] uses only induced subgraphs
set_option linter.style.category_answer false in
/-- Is there a graph with $\aleph_2$ vertices and chromatic number $\aleph_2$ such that every
subgraph on $\aleph_1$ vertices has chromatic number $\leq\aleph_0$?

This question is **independent of ZFC** (and of ZFC + GCH), so the statement carries
`answer(sorry)`. In the terminology of [LHR19, §2.1] it asks for an
$(\aleph_0, \aleph_2)$-chromatic graph of size $\aleph_2$: Baumgartner [Bau84] showed that the
existence of such a graph is consistent with GCH, while Foreman and Laver [FL88] showed that,
relative to a large cardinal hypothesis, its non-existence is consistent with GCH as well. -/
@[category research solved, AMS 5]
theorem erdos_918.parts.i :
    answer(sorry) ↔ ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀ := by
  sorry

/-- Is there a graph with $\aleph_{\omega+1}$ vertices and chromatic number $\aleph_1$ such that
every subgraph on $\aleph_\omega$ vertices has chromatic number $\leq\aleph_0$? -/
-- Formalisation note: `ω` here is `Ordinal.omega0`, from `open scoped Ordinal`, as in 623.lean.
-- It is the fixed first infinite ordinal, not a variable: `variants.erdos_hajnal` settles every
-- finite `k`, and `ℵ_ω` is the limit of that family, so this asks the single next case.
@[category research open, AMS 5]
theorem erdos_918.parts.ii :
    answer(sorry) ↔
    ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W = ℵ_ ω), (G.induce W).chromaticCardinal ≤ ℵ₀ := by
  sorry

-- Formalisation note: for the `≤ ℵ₀` direction this is the same question as `parts.i`, not a
-- separate one. Every subgraph on `W` is contained in the induced subgraph on `W`, so its
-- chromatic cardinal is no larger; and the top subgraph induced on `W` has `coe` equal to
-- `G.induce W`. So the two quantifications are equivalent and the answers cannot differ. The
-- `= ℵ₀` pair below is genuinely different, because an edgeless subgraph has chromatic
-- cardinal `1`, and that is the source's own reason for the impossibility there.
-- In particular this question is independent of ZFC as well, see `erdos_918.parts.i`.
set_option linter.style.category_answer false in
/-- Is there a graph with $\aleph_2$ vertices and chromatic number $\aleph_2$ such that every
subgraph on $\aleph_1$ vertices has chromatic number $\leq\aleph_0$? -/
@[category research solved, AMS 5]
theorem erdos_918.variants.all_subgraphs.parts.i :
    answer(sorry) ↔ ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (H : G.Subgraph) (_ : #H.verts = ℵ₁), H.coe.chromaticCardinal ≤ ℵ₀ := by
  sorry

/-- Is there a graph with $\aleph_{\omega+1}$ vertices and chromatic number $\aleph_1$ such that
every subgraph on $\aleph_\omega$ vertices has chromatic number $\leq\aleph_0$? -/
@[category research open, AMS 5]
theorem erdos_918.variants.all_subgraphs.parts.ii :
    answer(sorry) ↔
      ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (H : G.Subgraph) (_ : #H.verts = ℵ_ ω), H.coe.chromaticCardinal ≤ ℵ₀ := by
  sorry

/-- Assuming the generalised continuum hypothesis, Erd\H{o}s and Hajnal [ErHa68b, Corollary 1]
proved that for every finite $k \geq 1$ there is a graph with chromatic number $\aleph_1$ and
$\aleph_k$ vertices where each subgraph on less than $\aleph_k$ vertices has chromatic number
$\leq \aleph_0$.

The GCH hypothesis is stated as $2^{\mathfrak{c}} = \mathfrak{c}^+$ for every infinite
cardinal $\mathfrak{c}$. -/
-- Formalisation note: [erdosproblems.com/918] states this result without the assumption that
-- the graph has ℵₖ vertices; with that assumption it is [ErHa68b, Corollary 1], which assumes
-- GCH (the unconditional Theorem 2 there produces graphs of size `exp_{k-1}(ℵ₀)⁺`).
@[category research solved, AMS 5]
theorem erdos_918.variants.erdos_hajnal (k : ℕ) (hk : 0 < k)
    (hGCH : ∀ c : Cardinal.{u}, ℵ₀ ≤ c → 2 ^ c = Order.succ c) :
    ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ k ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W < ℵ_ k), (G.induce W).chromaticCardinal ≤ ℵ₀ := by
  sorry

/-- In [Er69b] the questions are stated with $= \aleph_0$ rather than $\leq\aleph_0$. This is
a likely typo since it can be shown that no such graph exists in this case.

This is the first question with induced subgraphs. -/
-- Formalisation note: the source states the impossibility for general subgraphs, in a
-- parenthetical, "assuming subgraph and not induced subgraph was intended", where an edgeless
-- subgraph does the job. For induced subgraphs a different argument is needed: pick any
-- `W` with `#W = ℵ₁`; a colouring of `G.induce W` with `ℵ₀` colours has an uncountable colour
-- class `I ⊆ W`, so `#I = ℵ₁` and `G.induce I` is edgeless with chromatic cardinal `1 ≠ ℵ₀`.
@[category textbook, AMS 5]
theorem erdos_918.variants.eq_aleph_0.parts.i :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal = ℵ₀ := by
  sorry

/-- In [Er69b] the questions are stated with $= \aleph_0$ rather than $\leq\aleph_0$. This is
a likely typo since it can be shown that no such graph exists in this case.

This is the first question with all subgraphs. -/
@[category textbook, AMS 5]
theorem erdos_918.variants.eq_aleph_0_all_subgraphs.parts.i :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (H : G.Subgraph) (_ : #H.verts = ℵ₁), H.coe.chromaticCardinal = ℵ₀ := by
  sorry

/-- In [Er69b] the questions are stated with $= \aleph_0$ rather than $\leq\aleph_0$. This is
a likely typo since it can be shown that no such graph exists in this case.

This is the second question with induced subgraphs. -/
-- Formalisation note: the source states the impossibility for general subgraphs, in a
-- parenthetical, "assuming subgraph and not induced subgraph was intended", where an edgeless
-- subgraph does the job. For induced subgraphs a different argument is needed: a colouring of
-- `G` with `ℵ₁` colours has a colour class of size `ℵ_ (ω + 1)` (as `ℵ_ (ω + 1)` is regular and
-- larger than `ℵ₁`); any `W` of size `ℵ_ ω` inside it induces an edgeless graph, with chromatic
-- cardinal `1 ≠ ℵ₀`. This uses that `ω ≠ 0`: with `ℵ₁` in place of `ℵ_ (ω + 1)` the complete
-- graph on `ℵ₁` vertices would be a counterexample.
@[category textbook, AMS 5]
theorem erdos_918.variants.eq_aleph_0.parts.ii :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W = ℵ_ ω), (G.induce W).chromaticCardinal = ℵ₀ := by
  sorry

/-- In [Er69b] the questions are stated with $= \aleph_0$ rather than $\leq\aleph_0$. This is
a likely typo since it can be shown that no such graph exists in this case.

This is the second question with all subgraphs. -/
@[category textbook, AMS 5]
theorem erdos_918.variants.eq_aleph_0_all_subgraphs.parts.ii :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (H : G.Subgraph) (_ : #H.verts = ℵ_ ω), H.coe.chromaticCardinal = ℵ₀ := by
  sorry

end Erdos918
