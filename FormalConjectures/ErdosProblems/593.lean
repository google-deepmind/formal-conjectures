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
**Erdős Problem 593 ($500)**: Characterize those finite 3-uniform hypergraphs which appear
in every 3-uniform hypergraph of chromatic number $> \aleph_0$.

A natural conjectural characterization, recorded here, is that the obligatory finite 3-uniform
hypergraphs are exactly the 2-colorable ones (Property B). The forward direction
(`IsObligatory → IsTwoColorable`) and converse (`IsTwoColorable → IsObligatory`) are stated as
separate variants below; in the graph case ($r = 2$), Erdős–Galvin–Hajnal [EGH75] proved the
analogous result (obligatory ⇔ bipartite).
-/
@[category research open, AMS 5]
theorem erdos_593 : answer(sorry) ↔
    ∀ (W : Type) [Fintype W] (F : ThreeUniformHypergraph W),
      IsObligatory F ↔ F.IsTwoColorable := by
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
    ∀ (W : Type) [Fintype W] (F : ThreeUniformHypergraph W),
      IsObligatory F → F.IsTwoColorable := by
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
    ∀ (W : Type) [Fintype W] (F : ThreeUniformHypergraph W),
      F.IsTwoColorable → IsObligatory F := by
  sorry

/--
**Conjunction of the two open implications gives the conjectured characterization**: if both
`obligatory_implies_two_colorable` and `two_colorable_implies_obligatory` hold, then the
characterization conjectured in `erdos_593` (`IsObligatory F ↔ F.IsTwoColorable`) follows by
elementary `Iff` manipulation.
-/
@[category test, AMS 5]
theorem erdos_593.variants.implications_combine
    (h₁ : ∀ (W : Type) [Fintype W] (F : ThreeUniformHypergraph W),
            IsObligatory F → F.IsTwoColorable)
    (h₂ : ∀ (W : Type) [Fintype W] (F : ThreeUniformHypergraph W),
            F.IsTwoColorable → IsObligatory F) :
    ∀ (W : Type) [Fintype W] (F : ThreeUniformHypergraph W),
      IsObligatory F ↔ F.IsTwoColorable := by
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
    {V : Type} (H : ThreeUniformHypergraph V) (hχ : ℵ₀ < H.chromaticCardinal) :
    ¬ Countable V := by
  intro hcount
  -- Since V is countable, there is an injection φ : V → ℕ.
  obtain ⟨φ, hφ⟩ := Countable.exists_injective_nat V
  -- The injection φ is a proper coloring using ℕ as the color type:
  -- each edge has card 3, so we can extract two distinct vertices with distinct images.
  have hprop : H.IsProperColoring φ := by
    intro e he
    -- Extract 3 distinct elements from e using H.uniform.
    have hcard : e.card = 3 := H.uniform e he
    -- Since e.card = 3 ≥ 2, there exist two distinct elements u ≠ v in e.
    have hge : 1 < e.card := by omega
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hge
    exact ⟨u, hu, v, hv, fun heq => huv (hφ heq)⟩
  -- So χ(H) ≤ #ℕ = ℵ₀.
  have hle : H.chromaticCardinal ≤ ℵ₀ := by
    apply csInf_le
    · -- The set {κ | ∃ C, #C = κ ∧ ∃ f, proper} is bounded below by 0.
      exact ⟨0, fun _ ⟨_, _, _, _⟩ => Cardinal.zero_le _⟩
    · exact ⟨ℕ, Cardinal.mk_nat, φ, hprop⟩
  exact absurd (lt_of_lt_of_le hχ hle) (lt_irrefl _)

/--
**No hyperedges implies chromatic cardinal ≤ 1**: A 3-uniform hypergraph with no edges can
be properly colored with a single color, so its chromatic cardinal is at most 1. In
particular, $\chi(H) > \aleph_0$ implies `H` has at least one hyperedge.
-/
@[category textbook, AMS 5]
theorem erdos_593.variants.nonempty_edges_if_large_chromatic
    {V : Type} (H : ThreeUniformHypergraph V) (hχ : ℵ₀ < H.chromaticCardinal) :
    H.edges.Nonempty := by
  by_contra hempty
  push_neg at hempty
  -- H has no edges (hempty : H.edges = ∅), so any coloring is proper.
  have hprop : H.IsProperColoring (fun _ : V => (0 : Fin 1)) := by
    intro e he
    rw [hempty] at he
    exact (Set.mem_empty_iff_false e).mp he |>.elim
  -- Hence χ(H) ≤ 1 < ℵ₀.
  have hle : H.chromaticCardinal ≤ 1 := by
    apply csInf_le
    · exact ⟨0, fun _ ⟨_, _, _, _⟩ => Cardinal.zero_le _⟩
    · refine ⟨Fin 1, ?_, fun _ => 0, hprop⟩
      simp
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
    {F₁ : ThreeUniformHypergraph W₁} {F₂ : ThreeUniformHypergraph W₂}
    (h12 : F₁.Appears F₂) (hObl : IsObligatory F₂) :
    IsObligatory F₁ := by
  intro V _hV H hχ
  obtain ⟨φ₂, hφ₂_inj, hφ₂_edge⟩ := hObl V H hχ
  obtain ⟨φ₁, hφ₁_inj, hφ₁_edge⟩ := h12
  refine ⟨φ₂ ∘ φ₁, hφ₂_inj.comp hφ₁_inj, fun e he => ?_⟩
  -- e.image (φ₂ ∘ φ₁) = (e.image φ₁).image φ₂ by Finset.image_image
  have heq : e.image (φ₂ ∘ φ₁) = (e.image φ₁).image φ₂ := by
    rw [Finset.image_image]
  rw [heq]
  exact hφ₂_edge _ (hφ₁_edge e he)

/--
**The empty hypergraph is trivially obligatory**: The 3-uniform hypergraph on `PEmpty` (no
vertices, no edges) appears in every hypergraph via the empty injection.

This degenerate case confirms the definition is well-formed.
-/
@[category textbook, AMS 5]
theorem erdos_593.variants.empty_hypergraph_obligatory :
    IsObligatory (W := PEmpty) ⟨∅, fun _ h => (Set.mem_empty_iff_false _).mp h |>.elim⟩ := by
  intro V _hV H _hχ
  exact ⟨IsEmpty.elim inferInstance, Function.injective_of_subsingleton _,
    fun _ h => (Set.mem_empty_iff_false _).mp h |>.elim⟩

end Erdos593
