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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 918

*References:*
- [erdosproblems.com/918](https://www.erdosproblems.com/918)
- [ErHa68b] Erdős, P. and Hajnal, A., On chromatic number of infinite graphs. (1968), 83--98.
- [Er69b] Erdős, P., Problems and results in chromatic graph theory. Proof Techniques in Graph Theory (Proc. Second Ann Arbor Graph Theory Conf., Ann Arbor, Mich., 1968) (1969), 27-35.
-/

universe u

open scoped Cardinal

namespace Erdos918

/-- Is there a graph with $\aleph_2$ vertices and chromatic number $\aleph_2$ such that every
subgraph on $\aleph_1$ vertices has chromatic number $\leq\aleph_0$? -/
-- Formalisation note: source material [ErHa68b] uses only induced subgraphs
@[category research open, AMS 5]
theorem erdos_918.parts.i :
    (∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀) ↔
    answer(sorry) := by
  sorry

/-- Is there a graph with $\aleph_{\omega+1}$ vertices and chromatic number $\aleph_1$ such that
every subgraph on $\aleph_\omega$ vertices has chromatic number $\leq\aleph_0$? -/
@[category research open, AMS 5]
theorem erdos_918.parts.ii (ω : Ordinal) :
    (∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W = ℵ_ ω), (G.induce W).chromaticCardinal ≤ ℵ₀) ↔
    answer(sorry) := by
  sorry

/-- Is there a graph with $\aleph_2$ vertices and chromatic number $\aleph_2$ such that every
subgraph on $\aleph_1$ vertices has chromatic number $\leq\aleph_0$? -/
-- Formalisation note: It is not clear whether this question for general subgraphs is open or not
@[category research open, AMS 5]
theorem erdos_918.variants.all_subgraphs.parts.i :
    (∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (H : G.Subgraph) (_ : #H.verts = ℵ₁), H.coe.chromaticCardinal ≤ ℵ₀) ↔
    answer(sorry) := by
  sorry

/-- Is there a graph with $\aleph_{\omega+1}$ vertices and chromatic number $\aleph_1$ such that
every subgraph on $\aleph_\omega$ vertices has chromatic number $\leq\aleph_0$? -/
@[category research open, AMS 5]
theorem erdos_918.variants.all_subgraphs.parts.ii (ω : Ordinal) :
    (∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (H : G.Subgraph) (_ : #H.verts = ℵ_ ω), H.coe.chromaticCardinal ≤ ℵ₀) ↔
    answer(sorry) := by
  sorry

/-- A question of Erd\H{o}s and Hajnal [ErHa68b], who proved that for every finite $k$
there is a graph with chromatic number $\aleph_1$ and $\aleph_k$ vertices where each subgraph on
less than $\aleph_k$ vertices has chromatic number $\leq \aleph_0$. -/
-- Formalisation note: the source is missing the assumption that the graph have ℵₖ vertices
-- which can be found in [ErHa68b]
@[category research solved, AMS 5]
theorem erdos_918.variants.erdos_hajnal (k : ℕ) : ∃ (V : Type u) (G : SimpleGraph V),
    #V = ℵ_ k ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W < ℵ_ k), (G.induce W).chromaticCardinal ≤ ℵ₀ :=
  sorry

/-- In [ErHa69] the questions are stated with $= \aleph_0$ rather than $\leq\aleph_0$. This is
a likely typo since it can be shown that no such graph exists in this case.

This is the first question with induced subgraphs. -/
@[category undergraduate, AMS 5]
theorem erdos_918.variants.eq_aleph_0.parts.i :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal = ℵ₀ := by
  sorry

/-- In [ErHa69] the questions are stated with $= \aleph_0$ rather than $\leq\aleph_0$. This is
a likely typo since it can be shown that no such graph exists in this case.

This is the first question with all subgraphs. -/
@[category high_school, AMS 5]
theorem erdos_918.variants.eq_aleph_0_all_subgraphs.parts.i :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (H : G.Subgraph) (_ : #H.verts = ℵ₁), H.coe.chromaticCardinal = ℵ₀ := by
  sorry

/-- In [ErHa69] the questions are stated with $= \aleph_0$ rather than $\leq\aleph_0$. This is
a likely typo since it can be shown that no such graph exists in this case.

This is the second question with induced subgraphs. -/
@[category undergraduate, AMS 5]
theorem erdos_918.variants.eq_aleph_0.parts.ii (ω : Ordinal) :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (W : Set V) (_ : #W = ℵ_ ω), (G.induce W).chromaticCardinal = ℵ₀ := by
  sorry

/-- In [ErHa69] the questions are stated with $= \aleph_0$ rather than $\leq\aleph_0$. This is
a likely typo since it can be shown that no such graph exists in this case.

This is the second question with all subgraphs. -/
@[category high_school, AMS 5]
theorem erdos_918.variants.eq_aleph_0_all_subgraphs.parts.ii (ω : Ordinal) :
    ¬∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ (ω + 1) ∧ G.chromaticCardinal = ℵ₁ ∧
      ∀ (H : G.Subgraph) (_ : #H.verts = ℵ_ ω), H.coe.chromaticCardinal = ℵ₀ := by
  sorry

end Erdos918
