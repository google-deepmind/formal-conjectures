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
-/

open Cardinal Set SimpleGraph

namespace Erdos593

/- ## Main open problem -/

/--
**Erdős Problem 593 (\$500)**: Characterize those finite 3-uniform hypergraphs which appear
in every 3-uniform hypergraph of chromatic number $> \aleph_0$.

A natural conjectural characterization, recorded here, is that the obligatory finite 3-uniform
hypergraphs are exactly the 2-colorable ones (Property B). The forward direction
(`F.IsObligatory → F.IsNColorable 2`) and converse (`F.IsNColorable 2 → F.IsObligatory`) are stated as
separate variants below; in the graph case ($r = 2$), Erdős–Galvin–Hajnal [EGH75] proved the
analogous result (obligatory ⇔ bipartite).
-/
@[category research open, AMS 5]
theorem erdos_593 : answer(sorry) ↔
    ∀ (W : Type) [Fintype W] (F : UniformHypergraph W 3),
      F.IsObligatory ↔ F.IsNColorable 2 := by
  sorry

/--
**Erdős Problem 593 — Necessary direction**: Every obligatory finite 3-uniform
hypergraph is 2-colorable.

This is the natural necessary condition for the conjectural characterization in `erdos_593`:
if a finite 3-uniform hypergraph `F` is not 2-colorable, one expects to construct a
hypergraph with large chromatic number that contains no copy of `F`.
-/
@[category research open, AMS 5]
theorem erdos_593.variants.obligatory_implies_two_colorable : answer(sorry) ↔
    ∀ (W : Type) [Fintype W] (F : UniformHypergraph W 3),
      F.IsObligatory → F.IsNColorable 2 := by
  sorry

/--
**Erdős Problem 593 — Sufficient direction**: Every finite 2-colorable 3-uniform
hypergraph is obligatory.

This is the converse direction of the `erdos_593` characterization: if 2-colorability
matches the graph-case characterization (bipartite ⇔ obligatory), then every 2-colorable
finite 3-uniform hypergraph must appear in every 3-uniform hypergraph of chromatic number
$> \aleph_0$.

Together with `erdos_593.variants.obligatory_implies_two_colorable`, this implies `erdos_593`.
-/
@[category research open, AMS 5]
theorem erdos_593.variants.two_colorable_implies_obligatory : answer(sorry) ↔
    ∀ (W : Type) [Fintype W] (F : UniformHypergraph W 3),
      F.IsNColorable 2 → F.IsObligatory := by
  sorry

/--
**Conjunction of the two open implications gives the conjectured characterization**: if both
`obligatory_implies_two_colorable` and `two_colorable_implies_obligatory` hold, then the
characterization conjectured in `erdos_593` (`F.IsObligatory ↔ F.IsNColorable 2`) follows by
elementary `Iff` manipulation.
-/
@[category test, AMS 5]
theorem erdos_593.variants.implications_combine
    (h₁ : ∀ (W : Type) [Fintype W] (F : UniformHypergraph W 3),
            F.IsObligatory → F.IsNColorable 2)
    (h₂ : ∀ (W : Type) [Fintype W] (F : UniformHypergraph W 3),
            F.IsNColorable 2 → F.IsObligatory) :
    ∀ (W : Type) [Fintype W] (F : UniformHypergraph W 3),
      F.IsObligatory ↔ F.IsNColorable 2 := by
  intro W _ F
  exact ⟨h₁ W F, h₂ W F⟩

/- ## Variants and partial results -/

/--
**Graph analogue — bipartite graphs are obligatory (Erdős–Galvin–Hajnal [EGH75])**:
For the 2-uniform (graph) case, a graph of chromatic cardinal $> \aleph_0$ must contain all
finite bipartite graphs. Specifically, for every finite bipartite graph `F` and every graph
`G` with chromatic cardinal $> \aleph_0$, there is a graph embedding from `F` into `G`.

This uses `Nonempty (F ↪g G)` (graph embedding), aligned with the injective vertex map
used in the hypergraph `Appears` definition.
-/
@[category research solved, AMS 5]
theorem erdos_593.variants.graph_case_bipartite_obligatory :
    answer(True) ↔
    ∀ (V : Type*) (G : SimpleGraph V),
      ℵ₀ < G.chromaticCardinal →
      ∀ (W : Type*) [Fintype W] (F : SimpleGraph W), F.IsBipartite →
        Nonempty (F ↪g G) := by
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
