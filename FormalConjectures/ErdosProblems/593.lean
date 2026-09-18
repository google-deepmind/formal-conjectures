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
# Erdős Problem 593

*References:*
- [erdosproblems.com/593](https://www.erdosproblems.com/593)
- [EGH75] Erdős, Paul and Galvin, Fred and Hajnal, András, On set-systems having large
  chromatic number and not containing prescribed subsystems.
  Infinite and finite sets (Colloq., Keszthely, 1973; dedicated to P. Erdős on his 60th
  birthday), Vol. I. Colloq. Math. Soc. János Bolyai 10, North-Holland (1975), 425–513.
- [Er95d] Erdős, Paul, Some of my favourite problems in various branches of combinatorics.
  Matematiche (Catania) 47 (1992), no. 2, 231–240 (1995).
- [EHR73] Erdős, Paul and Hajnal, András and Rothschild, Bruce, On chromatic number of graphs
  and set-systems. Cambridge Summer School in Mathematical Logic (Cambridge, 1971),
  Lecture Notes in Math. 337, Springer (1973), 531–538.
-/

open Cardinal Set SimpleGraph

namespace Erdos593

/- ## Main open problem -/

/--
**Erdős Problem 593 (\$500)**: Characterize those finite 3-uniform hypergraphs which appear
in every 3-uniform hypergraph of chromatic number $> \aleph_0$.

The answer is the set of obligatory finite 3-uniform hypergraphs, represented here on the
labelled vertex sets `Fin n`.

Two-colorability (Property B) is a necessary condition, see
`erdos_593.variants.obligatory_implies_two_colorable`, but it is not sufficient: two triples
sharing a pair form a 2-colorable hypergraph that is not obligatory, see
`erdos_593.variants.common_pair_not_obligatory`. In the graph case ($r = 2$) the problem is
completely solved by Erdős–Galvin–Hajnal [EGH75]: the obligatory graphs are exactly the finite
bipartite graphs.

A resolution has been claimed by E. Li (arXiv:2606.24882, 2026); at the time of writing
erdosproblems.com still lists the problem as open.
-/
@[category research open, AMS 5]
theorem erdos_593 :
    {p : Σ n : ℕ, UniformHypergraph (Fin n) 3 | p.2.IsObligatory} = answer(sorry) := by
  sorry

/--
**Necessary direction**: every obligatory finite 3-uniform hypergraph is 2-colorable.

This follows from two constructions in [EGH75]. By [EHR73] (see [EGH75, p. 426]) there are
3-uniform hypergraphs of arbitrarily large chromatic number consisting of edge-disjoint
triples, so an obligatory `F` is linear (no two edges share two vertices). By the remark
preceding [EGH75, Theorem 10.9] there are, for every infinite cardinal $\kappa$, 3-uniform
hypergraphs of chromatic number $> \kappa$ all of whose linear sub-hypergraphs are
2-colorable. An obligatory `F` appears in such a hypergraph, hence is 2-colorable.
-/
@[category research solved, AMS 5]
theorem erdos_593.variants.obligatory_implies_two_colorable : answer(True) ↔
    ∀ (W : Type) [Fintype W] (F : UniformHypergraph W 3),
      F.IsObligatory → F.IsNColorable 2 := by
  sorry

/--
**Sufficient direction fails**: it is not the case that every finite 2-colorable 3-uniform
hypergraph is obligatory.

The hypergraph `commonPair` with edges $\{0,1,2\}$ and $\{0,1,3\}$ is 2-colorable but does
not appear in the 3-uniform hypergraphs of large chromatic number consisting of edge-disjoint
triples constructed in [EHR73], see `erdos_593.variants.common_pair_not_obligatory`.
-/
@[category research solved, AMS 5]
theorem erdos_593.variants.two_colorable_implies_obligatory : answer(False) ↔
    ∀ (W : Type) [Fintype W] (F : UniformHypergraph W 3),
      F.IsNColorable 2 → F.IsObligatory := by
  sorry

/-- The 3-uniform hypergraph on four vertices consisting of two triples sharing a pair,
$\{0,1,2\}$ and $\{0,1,3\}$. -/
def commonPair : UniformHypergraph (Fin 4) 3 :=
  UniformHypergraph.ofFinset {{0, 1, 2}, {0, 1, 3}} (by unfold Finset.IsUniform; decide)

/-- Two triples sharing a pair are 2-colorable: color the shared pair with one color and the
remaining two vertices with the other. -/
@[category test, AMS 5]
theorem erdos_593.variants.commonPair_isTwoColorable : commonPair.IsNColorable 2 :=
  ⟨fun i => if i.val < 2 then 0 else 1, by
    exact (UniformHypergraph.isProperColoring_ofFinset_iff
      ({{0, 1, 2}, {0, 1, 3}} : Finset (Finset (Fin 4)))
      (by unfold Finset.IsUniform; decide) _).mpr (by unfold Finset.IsProperHypergraphColoring; decide)⟩

/--
Two triples sharing a pair are **not** obligatory: by [EHR73] (see [EGH75, p. 426]) there are
3-uniform hypergraphs of arbitrarily large chromatic number consisting of edge-disjoint
triples, and `commonPair` does not appear in any of them.
-/
@[category research solved, AMS 5]
theorem erdos_593.variants.common_pair_not_obligatory : ¬ commonPair.IsObligatory := by
  sorry

/- ## Variants and partial results -/

/--
**Graph analogue — bipartite graphs are obligatory (Erdős–Galvin–Hajnal [EGH75])**:
For the 2-uniform (graph) case, a graph of chromatic cardinal $> \aleph_0$ must contain all
finite bipartite graphs. Specifically, for every finite bipartite graph `F` and every graph
`G` with chromatic cardinal $> \aleph_0$, there is a graph embedding from `F` into `G`.

This uses `F ⊑ G` (`SimpleGraph.IsContained`, an injective graph homomorphism), aligned with
the injective edge-preserving map used in the hypergraph `Appears` definition. A graph embedding
`F ↪g G` would require an induced copy, which the theorem does not provide.
-/
@[category research solved, AMS 5]
theorem erdos_593.variants.graph_case_bipartite_obligatory :
    answer(True) ↔
    ∀ (V : Type*) (G : SimpleGraph V),
      ℵ₀ < G.chromaticCardinal →
      ∀ (W : Type*) [Fintype W] (F : SimpleGraph W), F.IsBipartite →
        F ⊑ G := by
  simp only [true_iff]
  -- This is the Erdős–Galvin–Hajnal theorem [EGH75].
  sorry

/--
**Graph analogue — no odd cycle is obligatory (Erdős–Galvin–Hajnal [EGH75])**:
For every odd $k \geq 3$, there exists a graph with chromatic cardinal $\aleph_1$ that
contains no cycle of length $k$. This shows the class of obligatory graphs is strictly
smaller than all finite graphs.
-/
@[category research solved, AMS 5]
theorem erdos_593.variants.graph_case_no_odd_cycle :
    answer(True) ↔
    ∀ k : ℕ, Odd k → 3 ≤ k →
      ∃ (V : Type*) (G : SimpleGraph V),
        G.chromaticCardinal = ℵ_ 1 ∧
        IsEmpty (cycleGraph k →g G) := by
  simp only [true_iff]
  -- This is the Erdős–Galvin–Hajnal theorem [EGH75].
  sorry

/--
**Vertices must be uncountable**: Every 3-uniform hypergraph with chromatic cardinal
$> \aleph_0$ must have an uncountable vertex set.

**Proof:** If `V` is countable, there exists an injection `φ : V → ℕ`. Using distinct natural
numbers as colors gives a proper coloring, so $\chi(H) \leq \#\mathbb{N} = \aleph_0$,
contradicting $\chi(H) > \aleph_0$.
-/
@[category textbook, AMS 5]
theorem erdos_593.variants.uncountable_vertices_if_large_chromatic
    {V : Type} (H : UniformHypergraph V 3) (hχ : ℵ₀ < H.chromaticCardinal) :
    ¬ Countable V := by
  intro hcount
  -- Since V is countable, there is an injection φ : V → ℕ.
  obtain ⟨φ, hφ⟩ := Countable.exists_injective_nat V
  have hprop := H.isProperColoring_of_injective (by decide) hφ
  have hle : H.chromaticCardinal ≤ ℵ₀ := by
    simpa using H.chromaticCardinal_le hprop
  exact absurd (lt_of_lt_of_le hχ hle) (lt_irrefl _)

/--
**No hyperedges implies chromatic cardinal ≤ 1**: A 3-uniform hypergraph with no edges can
be properly colored with a single color, so its chromatic cardinal is at most 1. In
particular, $\chi(H) > \aleph_0$ implies `H` has at least one hyperedge.
-/
@[category textbook, AMS 5]
theorem erdos_593.variants.nonempty_edges_if_large_chromatic
    {V : Type} (H : UniformHypergraph V 3) (hχ : ℵ₀ < H.chromaticCardinal) :
    H.edgeSet.Nonempty := by
  by_contra! hempty
  -- H has no edges (hempty : H.edgeSet = ∅), so any coloring is proper.
  have hprop : H.IsProperColoring (fun _ : V => (0 : Fin 1)) := by
    intro e he
    rw [hempty] at he
    exact (Set.mem_empty_iff_false e).mp he |>.elim
  -- Hence χ(H) ≤ 1 < ℵ₀.
  have hle : H.chromaticCardinal ≤ 1 := by
    simpa using H.chromaticCardinal_le hprop
  have h1le : (1 : Cardinal) ≤ ℵ₀ := le_of_lt Cardinal.one_lt_aleph0
  exact absurd (lt_of_lt_of_le hχ (hle.trans h1le)) (lt_irrefl _)

/--
**Monotonicity of the obligatory property**: If `F₁` appears in `F₂` and `F₂` is obligatory,
then `F₁` is also obligatory.

**Proof:** For any `H` with $\chi(H) > \aleph_0$, since `F₂` is obligatory, `F₂` appears
in `H` via some injection `φ₂`. Since `F₁` appears in `F₂` via `φ₁`, the composition
`φ₂ ∘ φ₁` witnesses that `F₁` appears in `H`.
-/
@[category textbook, AMS 5]
theorem erdos_593.variants.obligatory_monotone
    {W₁ W₂ : Type} [Fintype W₁] [Fintype W₂] [DecidableEq W₂]
    {F₁ : UniformHypergraph W₁ 3} {F₂ : UniformHypergraph W₂ 3}
    (h12 : F₁.Appears F₂) (hObl : F₂.IsObligatory) :
    F₁.IsObligatory := by
  intro V _hV H hχ
  exact h12.trans (hObl V H hχ)

/--
**The empty hypergraph is trivially obligatory**: The 3-uniform hypergraph on `PEmpty` (no
vertices, no edges) appears in every hypergraph via the empty injection.

This degenerate case confirms the definition is well-formed.
-/
@[category textbook, AMS 5]
theorem erdos_593.variants.empty_hypergraph_obligatory :
    UniformHypergraph.IsObligatory (W := PEmpty) (k := 3)
      (UniformHypergraph.ofFinset ∅ (by simp [Finset.IsUniform])) := by
  intro V _hV H _hχ
  exact ⟨IsEmpty.elim inferInstance, Function.injective_of_subsingleton _,
    by simp [UniformHypergraph.ofFinset, Hypergraph.ofEdgeFamily, Hypergraph.image]⟩

end Erdos593
