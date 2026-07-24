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
# Sidorenko's conjecture (1993)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Sidorenko%27s_conjecture)
* [Si93] Sidorenko, A. (1993). "A correlation inequality for bipartite graphs."
  *Graphs Combin.* 9, pp. 201--204.
* [CoFo10] Conlon, D. and Fox, J. (2010). "Bounds for graph regularity and removal lemmas."
  *Geom. Funct. Anal.* 22, pp. 1191--1256.
* [KLL18] Kim, J.H., Lee, C., Lee, J. (2018). "Two approaches to Sidorenko's conjecture."
  *Trans. Amer. Math. Soc.* 370, pp. 8515--8552.
* [ArXiv2605] [arXiv:2605.14138](https://arxiv.org/abs/2605.14138)
-/

open Classical Finset SimpleGraph LimitObjects MeasureTheory

namespace SidorenkoConjecture

open LimitObjects

/- ## Homomorphism density

We use `SimpleGraph.homCount` / `SimpleGraph.homDensity` from
`FormalConjecturesForMathlib.Combinatorics.SimpleGraph.HomDensity` for finite host graphs,
and `graphonHomDensity` / `graphonEdgeDensity` from
`FormalConjecturesForMathlib.Combinatorics.LimitObjects.Graphon` for graphons on measure spaces. -/

variable {V W : Type*}

/- ## The conjecture -/

/--
**Sidorenko's conjecture (1993).**

For every finite bipartite simple graph $H$ and every finite simple graph $G$:
$t(H, G) \ge t(K_2, G)^{e(H)}$, where $K_2$ denotes the single-edge graph on 2 vertices
(i.e. `completeGraph (Fin 2)`).
-/
@[category research open, AMS 5]
theorem sidorenko_conjecture : answer(sorry) ↔
    ∀ {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] [Nonempty W]
      (H : SimpleGraph V) (G : SimpleGraph W)
      [DecidableRel H.Adj] [DecidableRel G.Adj],
      H.IsBipartite →
      homDensity (completeGraph (Fin 2)) G ^ H.edgeFinset.card ≤ homDensity H G := by
  sorry

/--
**Sidorenko's conjecture for graphons (1993).**

For every finite bipartite simple graph $H$ and every graphon $W$ on $[0, 1]$ with Lebesgue measure:
$t(H, W) \ge t(K_2, W)^{e(H)}$, where $t(K_2, W) = p(W)$ is the edge density of $W$,
and $t(H, W)$ is the graphon homomorphism density of $H$ in $W$.
-/
@[category research open, AMS 5]
theorem sidorenko_conjecture_graphon : answer(sorry) ↔
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj],
      H.IsBipartite →
      ∀ (W : Graphon),
        (graphonEdgeDensity W) ^ H.edgeFinset.card ≤ graphonHomDensity H W := by
  sorry

/- ## Proved graphon special cases -/

/--
**Case: `H` is a tree (Sidorenko 1993, graphon version).**

If `H` is a finite tree then Sidorenko's inequality holds for all graphons on $[0, 1]$.
-/
@[category research solved, AMS 5]
theorem sidorenko_tree_graphon {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hTree : H.IsTree)
    (W : LimitObjects.Graphon) :
    (graphonEdgeDensity W) ^ H.edgeFinset.card ≤ graphonHomDensity H W := by
  sorry

/--
**Case: `H = C_{2k}` is an even cycle (Sidorenko 1993, graphon version).**

Every even cycle $C_{2k}$ satisfies Sidorenko's inequality for all graphons on $[0, 1]$.
-/
@[category research solved, AMS 5]
theorem sidorenko_even_cycle_graphon (k : ℕ) (hk : 1 ≤ k)
    (W : LimitObjects.Graphon) :
    (graphonEdgeDensity W) ^ (cycleGraph (2 * k)).edgeFinset.card ≤
      graphonHomDensity (cycleGraph (2 * k)) W := by
  sorry

/--
**Case: `H = K_{a,b}` is a complete bipartite graph (Sidorenko 1993, graphon version).**

Every complete bipartite graph $K_{a,b}$ satisfies Sidorenko's inequality for all graphons on $[0, 1]$.
-/
@[category research solved, AMS 5]
theorem sidorenko_completeBipartiteGraph_graphon {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (W : LimitObjects.Graphon) :
    (graphonEdgeDensity W) ^ (completeBipartiteGraph A B).edgeFinset.card ≤
      graphonHomDensity (completeBipartiteGraph A B) W := by
  sorry

/- ## Tournament Anti-Sidorenko (TAS) Trees Conjecture -/

/--
**Tournament Anti-Sidorenko (TAS) Trees Conjecture.**

For every finite undirected tree $T$, there exists an orientation $\vec{T}$ of its edges such that
for any finite tournament $G$, the homomorphism density satisfies:
$$ t_{\vec{T}}(G) \le 2^{-e(T)} $$
where $e(T)$ is the total number of edges in $T$.
-/
@[category research open, AMS 5]
theorem tournament_anti_sidorenko_trees_conjecture : answer(sorry) ↔
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
      T.IsTree →
      ∃ (D : Digraph V),
        D.IsOrientation T ∧
        ∀ {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
          (G : Digraph W) [DecidableRel G.Adj],
          G.IsTournament →
          Digraph.homDensity D G ≤ (1 / 2 : ℝ) ^ T.edgeFinset.card := by
  sorry

/--
**Tournament Anti-Sidorenko (TAS) Trees Conjecture (Tournamenton limit version).**

For every finite undirected tree $T$, there exists an orientation $\vec{T}$ of its edges such that
for every tournamenton $W : [0, 1]^2 \to [0, 1]$, the homomorphism density satisfies:
$$ t_{\vec{T}}(W) \le 2^{-e(T)} $$
where $e(T)$ is the total number of edges in $T$.
-/
@[category research open, AMS 5]
theorem tournament_anti_sidorenko_trees_conjecture_tournamenton : answer(sorry) ↔
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
      T.IsTree →
      ∃ (D : Digraph V),
        D.IsOrientation T ∧
        ∀ (W : LimitObjects.Tournamenton),
          tournamentonHomDensity D W ≤ (1 / 2 : ℝ) ^ T.edgeFinset.card := by
  sorry

/--
**TAS Trees Conjecture: Trees with a single even-degree vertex.**

Proven case of TAS Trees Conjecture: any tree containing exactly one vertex of even degree
possesses an orientation satisfying the Tournament Anti-Sidorenko inequality $t_{\vec{T}}(G) \le 2^{-e(T)}$.
-/
@[category research solved, AMS 5]
theorem tournament_anti_sidorenko_single_even_degree_tree {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hTree : T.IsTree)
    (hEven : (Finset.univ.filter (fun v => Even (T.degree v))).card = 1) :
    ∃ (D : Digraph V),
      D.IsOrientation T ∧
      ∀ {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
        (G : Digraph W) [DecidableRel G.Adj],
        G.IsTournament →
        Digraph.homDensity D G ≤ (1 / 2 : ℝ) ^ T.edgeFinset.card := by
  sorry

/--
**The $(2,3,4)$-spider tree.**
A tree composed of three paths of lengths 2, 3, and 4 joined at a single central vertex.
-/
def IsSpider234 {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) : Prop :=
  T.IsTree ∧ Fintype.card V = 10 ∧
  ∃ (center l₁ l₂ l₃ : V),
    T.degree center = 3 ∧
    l₁ ≠ l₂ ∧ l₁ ≠ l₃ ∧ l₂ ≠ l₃ ∧
    T.degree l₁ = 1 ∧ T.degree l₂ = 1 ∧ T.degree l₃ = 1 ∧
    ({T.dist center l₁, T.dist center l₂, T.dist center l₃} : Multiset ℕ) = {2, 3, 4}

/--
**TAS Trees Conjecture: The $(2,3,4)$-spider tree (Solved case).**

The $(2,3,4)$-spider tree satisfies the Tournament Anti-Sidorenko Trees Conjecture.

*Reference:*
* [ArXiv 2605.14138](https://arxiv.org/abs/2605.14138)
-/
@[category research solved, AMS 5]
theorem tournament_anti_sidorenko_spider234 {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hSpider : IsSpider234 T) :
    ∃ (D : Digraph V),
      D.IsOrientation T ∧
      ∀ {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
        (G : Digraph W) [DecidableRel G.Adj],
        G.IsTournament →
        Digraph.homDensity D G ≤ (1 / 2 : ℝ) ^ T.edgeFinset.card := by
  sorry

/- ## Proved special cases -/

/--
**Case `H = K_2` (single edge): Sidorenko's inequality holds trivially with equality.**

When `H` is `K_2` (the single-edge graph on 2 vertices), `e(H) = 1`, so the RHS of Sidorenko's
inequality is just `t(K_2, G)^1 = t(K_2, G) = t(H, G)`, which equals the LHS. Hence the
inequality holds as equality.

The proof records that `(completeGraph (Fin 2)).edgeFinset.card = 1` and then reduces the claim
to `t(K_2, G) ≤ t(K_2, G)`, which is `le_refl`.
-/
@[category research solved, AMS 5]
theorem sidorenko_K2 {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] :
    homDensity (completeGraph (Fin 2)) G ^
      ((completeGraph (Fin 2)).edgeFinset.card) ≤
      homDensity (completeGraph (Fin 2)) G := by
  -- `(completeGraph (Fin 2)).edgeFinset.card = 1`, so the inequality is `x^1 ≤ x`, i.e. `x ≤ x`.
  have hK2 : (completeGraph (Fin 2)).edgeFinset.card = 1 := by
    rw [SimpleGraph.card_edgeFinset_completeGraph_fin, Nat.choose_self]
  rw [hK2, pow_one]

/- ## Sidorenko for `K_{2,2}`: auxiliary lemmas -/

/-- `edgeCount` of `K_{2,2}` (complete bipartite graph on `Fin 2 + Fin 2`) is `4`.

The four edges are `{inl 0, inr 0}`, `{inl 0, inr 1}`, `{inl 1, inr 0}`, `{inl 1, inr 1}`. -/
@[category API, AMS 5]
lemma edgeCount_completeBipartiteGraph_fin_two :
    (completeBipartiteGraph (Fin 2) (Fin 2)).edgeFinset.card = 4 := by
  -- Every vertex of `K_{2,2}` has degree 2, and there are 4 vertices; so by the
  -- handshake formula `2 * #E = ∑ deg = 4 * 2 = 8`, hence `#E = 4`.
  have hdeg : ∀ v : Fin 2 ⊕ Fin 2, (completeBipartiteGraph (Fin 2) (Fin 2)).degree v = 2 := by
    intro v
    rw [show (completeBipartiteGraph (Fin 2) (Fin 2)).degree v =
        ((completeBipartiteGraph (Fin 2) (Fin 2)).neighborFinset v).card from rfl]
    cases v with
    | inl i =>
      -- Neighbours of `inl i`: exactly `{inr 0, inr 1}`.
      rw [neighborFinset_eq_filter]
      rw [show (Finset.univ : Finset (Fin 2 ⊕ Fin 2)).filter
          (fun w => (completeBipartiteGraph (Fin 2) (Fin 2)).Adj (Sum.inl i) w)
          = {Sum.inr (0 : Fin 2), Sum.inr (1 : Fin 2)} from ?_]
      · decide
      · ext w
        cases w with
        | inl k =>
          simp [completeBipartiteGraph_adj]
        | inr k =>
          simp [completeBipartiteGraph_adj]
          fin_cases k <;> decide
    | inr j =>
      rw [neighborFinset_eq_filter]
      rw [show (Finset.univ : Finset (Fin 2 ⊕ Fin 2)).filter
          (fun w => (completeBipartiteGraph (Fin 2) (Fin 2)).Adj (Sum.inr j) w)
          = {Sum.inl (0 : Fin 2), Sum.inl (1 : Fin 2)} from ?_]
      · decide
      · ext w
        cases w with
        | inl k =>
          simp [completeBipartiteGraph_adj]
          fin_cases k <;> decide
        | inr k =>
          simp [completeBipartiteGraph_adj]
  have h : 2 * ((completeBipartiteGraph (Fin 2) (Fin 2)).edgeFinset).card =
      ∑ v : Fin 2 ⊕ Fin 2, (completeBipartiteGraph (Fin 2) (Fin 2)).degree v := by
    rw [← (completeBipartiteGraph (Fin 2) (Fin 2)).sum_degrees_eq_twice_card_edges]
  rw [Finset.sum_congr rfl (fun v _ => hdeg v)] at h
  simp at h
  omega

/-- **Homomorphism count of `K_2` into `G` equals `2 · #edgeFinset`.**

A homomorphism `K_2 →g G` is the same data as an ordered pair `(f 0, f 1)` of distinct
vertices with `G.Adj (f 0) (f 1)`. These are in bijection with the `Dart`s of `G`, and
`#Darts(G) = 2 · #E(G)` by `dart_card_eq_twice_card_edges`. -/
@[category API, AMS 5]
lemma homCount_completeGraph_fin_two_eq_two_mul_card_edgeFinset
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] :
    homCount (completeGraph (Fin 2)) G = 2 * #G.edgeFinset := by
  -- Build a bijection `(completeGraph (Fin 2) →g G) ≃ G.Dart`.
  unfold homCount
  rw [← G.dart_card_eq_twice_card_edges]
  -- Now: `Fintype.card (completeGraph (Fin 2) →g G) = Fintype.card G.Dart`.
  refine Fintype.card_congr ?_
  refine
    { toFun := fun f =>
        ⟨(f 0, f 1), f.map_adj (by decide : (completeGraph (Fin 2)).Adj 0 1)⟩
      invFun := fun d =>
        { toFun := fun i => if i = 0 then d.fst else d.snd
          map_rel' := fun {a b} hab => by
            -- `completeGraph (Fin 2)` adjacency means `a ≠ b`.
            simp only [completeGraph, top_adj] at hab
            -- `a, b ∈ Fin 2` with `a ≠ b` means `{a, b} = {0, 1}`.
            fin_cases a <;> fin_cases b
            · simp at hab
            · exact d.adj
            · exact d.adj.symm
            · simp at hab }
      left_inv := fun f => by
        ext i
        fin_cases i <;> simp
      right_inv := fun d => by
        cases d
        rfl }

/-- **The `Hom(K_{2,2}, G)` decomposition.** The number of homomorphisms from
`K_{2,2}` to `G` equals `∑_{(a, b) ∈ W × W} |N(a) ∩ N(b)|^2`, where `N(v)` is the
neighbourhood of `v` in `G`. Equivalently, summing over *ordered* pairs
`(b₀, b₁) ∈ W × W` and counting common neighbours squared.

**Math.** A homomorphism `K_{2,2} →g G` is an assignment `f : Fin 2 ⊕ Fin 2 → W`
with `G.Adj (f (inl i)) (f (inr j))` for all `i, j ∈ Fin 2`. Equivalently, choose
`(a₀, a₁) := (f (inl 0), f (inl 1))` arbitrarily in `W × W` and require
`(f (inr 0), f (inr 1))` to both lie in `N(a₀) ∩ N(a₁)`. The count is thus
`∑_{(a₀, a₁)} |N(a₀) ∩ N(a₁)|²`.

**Proof.** Construct an explicit bijection
`(K_{2,2} →g G) ≃ Σ (p : W × W), (N(p.1) ∩ N(p.2)) × (N(p.1) ∩ N(p.2))`
by sending a homomorphism `f` to `⟨(f (inl 0), f (inl 1)), ⟨f (inr 0), f (inr 1)⟩⟩`.
The total cardinality of the sigma-product is then
`∑_p (Fintype.card (N(p.1) ∩ N(p.2)))² = ∑_p |N(p.1) ∩ N(p.2)|²`. -/
@[category API, AMS 5]
lemma homCount_completeBipartiteGraph_fin_two_eq_sum_inter_sq
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] :
    (homCount (completeBipartiteGraph (Fin 2) (Fin 2)) G : ℝ) =
      ∑ p : W × W,
        (((G.neighborFinset p.1) ∩ (G.neighborFinset p.2)).card : ℝ) ^ 2 := by
  -- Reduce to a ℕ identity then cast.
  have hNat : homCount (completeBipartiteGraph (Fin 2) (Fin 2)) G =
      ∑ p : W × W,
        ((G.neighborFinset p.1) ∩ (G.neighborFinset p.2)).card ^ 2 := by
    unfold homCount
    -- Build a `Fintype`-card equivalence between `K_{2,2} →g G` and
    -- the sigma type `Σ (p : W × W), (N(p.1) ∩ N(p.2)) × (N(p.1) ∩ N(p.2))`.
    -- A homomorphism `f : K_{2,2} →g G` is determined by the four values
    -- `(f (inl 0), f (inl 1), f (inr 0), f (inr 1))` with `(inr j)`
    -- adjacent to `(inl i)` for all `i, j`.  So parameterise by
    -- `a₀ := f (inl 0)`, `a₁ := f (inl 1)`, then `(b₀, b₁) := (f (inr 0), f (inr 1))`
    -- must both lie in `N(a₀) ∩ N(a₁)`.
    let KBip := completeBipartiteGraph (Fin 2) (Fin 2)
    -- Define the target type parameterised in `p = (a₀, a₁)`.
    -- Step 1: `card (K_{2,2} →g G) = card (Σ p, (N(p.1) ∩ N(p.2)) × (N(p.1) ∩ N(p.2)))`.
    have hEquiv : (KBip →g G) ≃
        Σ p : W × W,
          ({a : W // a ∈ G.neighborFinset p.1 ∩ G.neighborFinset p.2} ×
            {a : W // a ∈ G.neighborFinset p.1 ∩ G.neighborFinset p.2}) := by
      refine
        { toFun := fun f =>
            ⟨(f (Sum.inl 0), f (Sum.inl 1)),
              ⟨⟨f (Sum.inr 0), ?_⟩, ⟨f (Sum.inr 1), ?_⟩⟩⟩
          invFun := fun x =>
            { toFun := fun v => match v with
                | Sum.inl 0 => x.1.1
                | Sum.inl 1 => x.1.2
                | Sum.inr 0 => x.2.1.val
                | Sum.inr 1 => x.2.2.val
              map_rel' := ?_ }
          left_inv := ?_
          right_inv := ?_ }
      all_goals (try (
        -- `f (Sum.inr j) ∈ N(f (Sum.inl 0)) ∩ N(f (Sum.inl 1))` for j = 0, 1.
        simp only [Finset.mem_inter, mem_neighborFinset]
        refine ⟨f.map_adj ?_, f.map_adj ?_⟩ <;>
          simp [KBip, completeBipartiteGraph_adj]))
      · -- Adjacency preservation for the inverse function.
        rintro a b hab
        rcases x with ⟨⟨a₀, a₁⟩, ⟨⟨b₀, hb₀⟩, ⟨b₁, hb₁⟩⟩⟩
        simp only [KBip, completeBipartiteGraph_adj] at hab
        simp only [Finset.mem_inter, mem_neighborFinset] at hb₀ hb₁
        match a, b, hab with
        | Sum.inl i, Sum.inr j, hab =>
          fin_cases i <;> fin_cases j <;>
            first | exact hb₀.1 | exact hb₀.2 | exact hb₁.1 | exact hb₁.2
        | Sum.inr j, Sum.inl i, hab =>
          fin_cases i <;> fin_cases j <;>
            first | exact (hb₀.1).symm | exact (hb₀.2).symm |
                    exact (hb₁.1).symm | exact (hb₁.2).symm
      · -- left_inv
        intro f
        ext v
        -- v : Fin 2 ⊕ Fin 2, enumerate cases.
        match v with
        | Sum.inl i => fin_cases i <;> rfl
        | Sum.inr j => fin_cases j <;> rfl
      · -- right_inv
        rintro ⟨⟨a₀, a₁⟩, ⟨⟨b₀, hb₀⟩, ⟨b₁, hb₁⟩⟩⟩
        rfl
    -- Step 2: use `Fintype.card_congr` and simplify the cardinality of the sigma-product.
    rw [Fintype.card_congr hEquiv]
    rw [Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro p _
    rw [Fintype.card_prod, sq]
    -- Rewrite each subtype cardinality to a finset cardinality.
    have hcard : Fintype.card
        {a : W // a ∈ G.neighborFinset p.1 ∩ G.neighborFinset p.2}
          = (G.neighborFinset p.1 ∩ G.neighborFinset p.2).card := Fintype.card_coe _
    rw [hcard]
  -- Cast ℕ identity to ℝ.
  have := congrArg (Nat.cast (R := ℝ)) hNat
  push_cast at this
  exact this

/-- **`K_{2,2}` count via a re-indexed sum.** Swapping the order of summation, the
`Hom(K_{2,2}, G)` count equals `∑_{a ∈ W} (G.degree a)²` summed over... wait, more
precisely: the sum `∑_{(b₀, b₁)} |N(b₀) ∩ N(b₁)|` (without the square) equals
`∑_a (G.degree a)²`, by swapping `(∑_{b₀, b₁} ∑_a [a ~ b₀][a ~ b₁]) = ∑_a (∑_b [a ~ b])²`.

This version of the identity is what appears in the Cauchy-Schwarz step. -/
@[category API, AMS 5]
lemma sum_inter_card_eq_sum_degree_sq
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] :
    ∑ p : W × W,
        (((G.neighborFinset p.1) ∩ (G.neighborFinset p.2)).card : ℝ) =
      ∑ a : W, ((G.degree a : ℝ)) ^ 2 := by
  -- Work in ℕ for the combinatorial part, then cast.
  have hNat : ∑ p : W × W, ((G.neighborFinset p.1) ∩ (G.neighborFinset p.2)).card =
      ∑ a : W, (G.degree a) ^ 2 := by
    -- `|N(b₀) ∩ N(b₁)| = ∑_a [a ∈ N(b₀)][a ∈ N(b₁)]`, so summing gives
    -- `∑_{b₀, b₁} |N(b₀) ∩ N(b₁)| = ∑_a (∑_{b₀} [b₀ ∈ N(a)])² = ∑_a deg(a)²`,
    -- using `b ∈ N(a) ↔ a ∈ N(b)` (`adj_comm`).
    calc ∑ p : W × W, ((G.neighborFinset p.1) ∩ (G.neighborFinset p.2)).card
        = ∑ p : W × W,
            ((Finset.univ : Finset W).filter
              (fun a => a ∈ G.neighborFinset p.1 ∧ a ∈ G.neighborFinset p.2)).card := by
          apply Finset.sum_congr rfl
          intro p _
          congr 1
          ext a
          simp [Finset.mem_inter]
      _ = ∑ p : W × W, ∑ a : W,
            (if a ∈ G.neighborFinset p.1 ∧ a ∈ G.neighborFinset p.2 then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro p _
          rw [Finset.card_filter]
      _ = ∑ a : W, ∑ p : W × W,
            (if a ∈ G.neighborFinset p.1 ∧ a ∈ G.neighborFinset p.2 then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ a : W, (∑ b : W, (if a ∈ G.neighborFinset b then 1 else 0)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [sq, Finset.sum_mul_sum]
          -- Goal: `∑ p : W × W, ite (a ∈ N p.1 ∧ a ∈ N p.2) 1 0 = ∑ p ∈ univ ×ˢ univ, ...`
          rw [show (Finset.univ : Finset (W × W)) = Finset.univ ×ˢ Finset.univ from
            (Finset.univ_product_univ).symm]
          rw [Finset.sum_product]
          apply Finset.sum_congr rfl
          intro b₀ _
          apply Finset.sum_congr rfl
          intro b₁ _
          by_cases h0 : a ∈ G.neighborFinset b₀ <;> by_cases h1 : a ∈ G.neighborFinset b₁ <;>
            simp [h0, h1]
      _ = ∑ a : W, (G.degree a) ^ 2 := by
          apply Finset.sum_congr rfl
          intro a _
          congr 1
          -- Want: `∑ b, ite (a ∈ N(b)) 1 0 = G.degree a`.
          rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
            smul_eq_mul, mul_one]
          rw [← card_neighborFinset_eq_degree]
          congr 1
          ext b
          simp [mem_neighborFinset, adj_comm]
  -- Cast to ℝ.
  have := congrArg (Nat.cast (R := ℝ)) hNat
  simp only [Nat.cast_sum, Nat.cast_pow] at this
  exact this

/--
**Case `H = K_{2,2}` (four-cycle, also called `C_4`): Sidorenko's conjecture holds, by
Cauchy–Schwarz.**

The textbook statement at `H = K_{2,2}` is
`t(K_2, G)^{e(K_{2,2})} = t(K_2, G)^4 ≤ t(K_{2,2}, G)`.

**Proof sketch.** Write `d(a) := G.degree a`. Then
- `homCount(K_2, G) = ∑_a d(a) = 2·|E(G)|` (handshaking).
- `homCount(K_{2,2}, G) = ∑_{b₀, b₁} |N(b₀) ∩ N(b₁)|²` (product structure of bipartite
  homomorphism).
- `∑_{b₀, b₁} |N(b₀) ∩ N(b₁)| = ∑_a d(a)²` (swap sums).
- Cauchy–Schwarz #1: `(∑_{b₀, b₁} |N(b₀) ∩ N(b₁)|)² ≤ |W|² · ∑_{b₀, b₁} |N(b₀) ∩ N(b₁)|²`.
- Cauchy–Schwarz #2: `(∑_a d(a))² ≤ |W| · ∑_a d(a)²`.
- Chain: `(∑_a d(a))⁴ ≤ |W|⁴ · homCount(K_{2,2}, G)`.
- Divide by `|W|^8` to get `t(K_2, G)^4 ≤ t(K_{2,2}, G)`.

The proof uses `Finset.sum_mul_sq_le_sq_mul_sq` (discrete Cauchy–Schwarz) from
`Mathlib.Algebra.Order.BigOperators.Ring.Finset`.

**Status (2026-04-22):** main theorem closed sorry-free. See [Si93].
-/
@[category research solved, AMS 5]
theorem sidorenko_K22 {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] :
    homDensity (completeGraph (Fin 2)) G ^
      ((completeBipartiteGraph (Fin 2) (Fin 2)).edgeFinset.card) ≤
      homDensity (completeBipartiteGraph (Fin 2) (Fin 2)) G := by
  -- Unfold `edgeCount` to `4`.
  rw [edgeCount_completeBipartiteGraph_fin_two]
  -- Dispatch the empty-vertex-type case.
  by_cases hW : IsEmpty W
  · -- With `W` empty: `homCount K_2 G = 0` (no functions `Fin 2 → W`), hence `homDensity = 0`.
    -- `homCount K_{2,2} G = 0` as well, but division by `0^4 = 0` still gives `0`.
    simp only [homDensity]
    have hcardW : Fintype.card W = 0 := Fintype.card_eq_zero
    rw [hcardW]
    -- The goal now involves `0 ^ _` in denominators. Both sides reduce to `0`.
    simp only [Fintype.card_fin, pow_succ, pow_zero, one_mul]
    -- Fin 2 has 2 elements, (Fin 2 ⊕ Fin 2) has 4.
    rw [show Fintype.card (Fin 2 ⊕ Fin 2) = 4 by decide]
    norm_num
  -- Now `W` is nonempty.
  haveI : Nonempty W := not_isEmpty_iff.mp hW
  have hWpos : 0 < (Fintype.card W : ℝ) := by exact_mod_cast Fintype.card_pos
  -- Unfold densities.
  unfold homDensity
  set n : ℕ := Fintype.card W with hn
  have hn_pos : 0 < (n : ℝ) := hWpos
  -- Cardinalities of the two `V` sides of `homDensity`.
  have hFin2 : Fintype.card (Fin 2) = 2 := by decide
  have hFin2sum : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by decide
  rw [hFin2, hFin2sum]
  -- Notation.
  set N : ℕ := homCount (completeGraph (Fin 2)) G with hN
  set M : ℕ := homCount (completeBipartiteGraph (Fin 2) (Fin 2)) G with hM
  -- Goal: `((N : ℝ) / n^2)^4 ≤ (M : ℝ) / n^4`.
  -- Multiply through by `n^8`: `N^4 * n^0 ≤ M * n^4`... but power combining is tricky.
  -- Instead: express as `N^4 ≤ M * n^4` then divide by `n^8 = (n^2)^4`.
  have h_main : (N : ℝ) ^ 4 ≤ (M : ℝ) * (n : ℝ) ^ 4 := by
    -- Plan:
    -- (1) `N = ∑ a, deg(a)` (from K_2 bijection + handshaking).
    have hN_expand : (N : ℝ) = ∑ a : W, (G.degree a : ℝ) := by
      rw [hN, homCount_completeGraph_fin_two_eq_two_mul_card_edgeFinset]
      rw [← G.sum_degrees_eq_twice_card_edges]
      push_cast; rfl
    -- (2) `M = ∑ (b₀, b₁) : W × W, |N(b₀) ∩ N(b₁)|²` (Hom K_{2,2} decomposition).
    have hM_expand : (M : ℝ) =
        ∑ p : W × W, (((G.neighborFinset p.1) ∩ (G.neighborFinset p.2)).card : ℝ) ^ 2 :=
      homCount_completeBipartiteGraph_fin_two_eq_sum_inter_sq G
    -- Define `S := ∑ (b₀, b₁), |N(b₀) ∩ N(b₁)|`. Then:
    -- - C-S #1: `S² ≤ n² · M`.
    -- - `S = ∑ a, deg(a)²` (swap sums).
    -- - C-S #2: `N² = (∑_a deg a)² ≤ n · ∑_a deg(a)² = n · S`.
    -- Combining: `N⁴ = (N²)² ≤ (n · S)² = n² · S² ≤ n² · (n² · M) = n⁴ · M`.
    set S : ℝ := ∑ p : W × W, (((G.neighborFinset p.1) ∩ (G.neighborFinset p.2)).card : ℝ)
      with hS
    -- S_nonneg
    have hS_nonneg : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
    -- Step A: S = ∑ a, deg(a)².
    have hS_eq_sumdeg_sq : S = ∑ a : W, ((G.degree a : ℝ)) ^ 2 :=
      sum_inter_card_eq_sum_degree_sq G
    -- Step B: C-S #2: `(∑_a deg a)² ≤ n · ∑_a deg(a)²`.
    have hCS2 : (∑ a : W, (G.degree a : ℝ)) ^ 2 ≤ (n : ℝ) * ∑ a : W, ((G.degree a : ℝ)) ^ 2 := by
      have hraw := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset W)
        (fun a => (G.degree a : ℝ)) (fun _ => (1 : ℝ))
      -- hraw : (∑ a ∈ univ, deg(a) * 1)^2 ≤ (∑ a ∈ univ, deg(a)^2) * ∑ a ∈ univ, 1^2
      simp only [mul_one, one_pow] at hraw
      -- After simp: `(∑_a deg a)² ≤ (∑_a deg a ²) * ∑_a 1`.
      have hcard : (∑ _a : W, (1 : ℝ)) = (n : ℝ) := by
        simp [Finset.sum_const, Finset.card_univ, ← hn]
      rw [hcard] at hraw
      linarith [hraw]
    -- Step C: C-S #1: `(∑ p, x(p))² ≤ n² · ∑ p, x(p)²` where `p : W × W` and `|W × W| = n²`.
    have hCS1 : S ^ 2 ≤ (n : ℝ) ^ 2 * (M : ℝ) := by
      have hraw := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (W × W))
        (fun p => (((G.neighborFinset p.1) ∩ (G.neighborFinset p.2)).card : ℝ))
        (fun _ => (1 : ℝ))
      simp only [mul_one, one_pow] at hraw
      have hcard : (∑ _p : W × W, (1 : ℝ)) = (n : ℝ) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ← hn]
        ring
      rw [hcard] at hraw
      rw [hS, hM_expand]
      linarith [hraw]
    -- Now chain.
    have hN_eq : (N : ℝ) = ∑ a : W, (G.degree a : ℝ) := hN_expand
    have hN2_le : (N : ℝ) ^ 2 ≤ (n : ℝ) * S := by
      rw [hN_eq, hS_eq_sumdeg_sq]; exact hCS2
    have hN_nonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
    have hn_nonneg : 0 ≤ (n : ℝ) := hn_pos.le
    have hn2_nonneg : 0 ≤ (n : ℝ) ^ 2 := by positivity
    -- N^4 = (N^2)^2 ≤ (n·S)^2 = n²·S² ≤ n²·(n²·M) = n⁴·M.
    have hN4_le : (N : ℝ) ^ 4 ≤ (n : ℝ) ^ 2 * S ^ 2 := by
      have : ((N : ℝ) ^ 2) ^ 2 ≤ ((n : ℝ) * S) ^ 2 := by
        apply sq_le_sq' (by nlinarith [sq_nonneg ((N : ℝ)^2 + (n : ℝ)*S)]) hN2_le
      calc (N : ℝ) ^ 4 = ((N : ℝ) ^ 2) ^ 2 := by ring
        _ ≤ ((n : ℝ) * S) ^ 2 := this
        _ = (n : ℝ) ^ 2 * S ^ 2 := by ring
    calc (N : ℝ) ^ 4 ≤ (n : ℝ) ^ 2 * S ^ 2 := hN4_le
      _ ≤ (n : ℝ) ^ 2 * ((n : ℝ) ^ 2 * (M : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hCS1 hn2_nonneg
      _ = (M : ℝ) * (n : ℝ) ^ 4 := by ring
  -- Turn `h_main : N^4 ≤ M * n^4` into the density inequality `(N/n²)^4 ≤ M/n⁴`.
  have hn4_pos : 0 < (n : ℝ) ^ 4 := by positivity
  have hn2_pos : 0 < (n : ℝ) ^ 2 := by positivity
  rw [div_pow, div_le_div_iff₀ (by positivity) hn4_pos]
  -- Goal: N^4 * n^4 ≤ M * (n^2)^4 = M * n^8.
  -- From h_main: N^4 ≤ M * n^4. Multiply both sides by n^4 > 0.
  have hmul := mul_le_mul_of_nonneg_right h_main hn4_pos.le
  -- hmul : N^4 * n^4 ≤ (M * n^4) * n^4
  nlinarith [hmul, sq_nonneg ((n : ℝ))]

/-- Consequence of `homDensity_le_one`: both sides of the Sidorenko K_{2,2}
inequality are bounded above by 1. This is a trivial consequence, recorded
as a sanity check on the helper infrastructure in
`FormalConjecturesForMathlib.Combinatorics.SimpleGraph.HomDensity`. -/
@[category API, AMS 5]
theorem sidorenko_K22_both_sides_bounded {W : Type*} [Fintype W] [Nonempty W]
    [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    homDensity (completeGraph (Fin 2)) G ≤ 1
    ∧ homDensity (completeBipartiteGraph (Fin 2) (Fin 2)) G ≤ 1 :=
  ⟨SimpleGraph.homDensity_le_one _ _, SimpleGraph.homDensity_le_one _ _⟩

/- ## Sidorenko for trees: auxiliary lemmas -/

/-- If the domain of `H` has at most one vertex, `H` has no edges.

**Proof.** `SimpleGraph.Adj` is irreflexive, so any adjacency `H.Adj u v` forces
`u ≠ v`; on a subsingleton that's impossible, so no edges exist. -/
@[category API, AMS 5]
lemma edgeCount_eq_zero_of_subsingleton {V : Type*} [Fintype V] [Subsingleton V]
    (H : SimpleGraph V) [DecidableRel H.Adj] : H.edgeFinset.card = 0 := by
  rw [Finset.card_eq_zero]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  rw [mem_edgeFinset] at he
  induction e with
  | h u v =>
    rw [mem_edgeSet] at he
    exact H.ne_of_adj he (Subsingleton.elim u v)

/-- If the domain of `H` has at most one vertex, every function `V → W` is a homomorphism
`H →g G`. Equivalently, `homCount H G = |W|^|V|`.

**Proof.** The adjacency `H.Adj u v` is irreflexive; on a subsingleton it is uninhabited,
so the homomorphism condition `H.Adj u v → G.Adj (f u) (f v)` is vacuous. Hence the
`coe : (H →g G) → (V → W)` map is a bijection. -/
@[category API, AMS 5]
lemma homCount_eq_of_subsingleton {V W : Type*} [Fintype V] [Fintype W]
    [Subsingleton V] [DecidableEq V] [DecidableEq W]
    (H : SimpleGraph V) (G : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel G.Adj] :
    homCount H G = (Fintype.card W) ^ (Fintype.card V) := by
  unfold homCount
  rw [← Fintype.card_fun]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun f => (f : V → W)
      invFun := fun f =>
        { toFun := f
          map_rel' := fun {u v} huv => (H.ne_of_adj huv (Subsingleton.elim u v)).elim }
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **Base case of Sidorenko for trees.** When the tree `H` has at most one vertex,
both sides of Sidorenko's inequality evaluate to `1` (there are no edges, and every
function is a homomorphism). Thus the inequality `1 ≤ 1` holds trivially.

This covers the `|V(T)| = 1` base case of the induction on tree size. -/
@[category research solved, AMS 5]
theorem sidorenko_tree_subsingleton {V W : Type} [Fintype V] [Fintype W]
    [Subsingleton V] [DecidableEq V] [DecidableEq W] [Nonempty W]
    (H : SimpleGraph V) (G : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel G.Adj] :
    homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G := by
  -- `H.edgeFinset.card = 0`, so LHS = `_ ^ 0 = 1`.
  rw [edgeCount_eq_zero_of_subsingleton H, pow_zero]
  -- `homDensity H G = |W|^|V| / |W|^|V| = 1`.
  have hWpos : 0 < Fintype.card W := Fintype.card_pos
  have hWpow : (0 : ℝ) < (Fintype.card W : ℝ) ^ Fintype.card V :=
    pow_pos (by exact_mod_cast hWpos) _
  rw [homDensity, homCount_eq_of_subsingleton H G]
  push_cast
  rw [div_self (ne_of_gt hWpow)]

/--
**Case: `H` is a tree (Sidorenko 1993).**

If `H` is a finite tree then Sidorenko's inequality holds.

**Proof idea (Sidorenko 1993):** by induction on the tree, applying Jensen / convexity. The
number of homomorphisms from a tree `T` with `v` vertices and `v - 1` edges into `G` factors
nicely in the degree sequence of `G`, and AM–GM / convexity gives the required lower bound.

**Current status (2026-04-22, partial):**
- The subsingleton base case (`|V(T)| ≤ 1`) is dispatched via `sidorenko_tree_subsingleton`.
- The main inductive step (leaf extraction + AM–GM on the degree sequence) is deferred;
  it requires a walk-parametrised homomorphism count for trees and a discrete Jensen
  inequality. See [Si93].

The full proof is left as `sorry`; the subsingleton case is closed.
-/
@[category research solved, AMS 5]
theorem sidorenko_tree {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] [Nonempty W]
    (H : SimpleGraph V) (G : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hTree : H.IsTree) :
    homDensity (completeGraph (Fin 2)) G ^ (H.edgeFinset.card) ≤ homDensity H G := by
  -- A tree's vertex set is nonempty.
  haveI : Nonempty V := hTree.isConnected.nonempty
  -- Split on whether `V` is a subsingleton.
  by_cases hSub : Subsingleton V
  · -- Base case: `|V| ≤ 1`, so `H` has no edges and both sides equal `1`.
    exact sidorenko_tree_subsingleton H G
  · -- Inductive step: `|V| ≥ 2`. This is the AM–GM / Jensen part of Sidorenko's proof.
    -- The argument: pick a leaf `v` of `H`, set `H' := H \ {v}` (a tree on `|V|-1`
    -- vertices), apply IH, then use the leaf decomposition
    -- `homCount H G = ∑ {φ : H' →g G}, G.degree (φ u)` (where `u` is the unique neighbour
    -- of `v` in `H`) and discrete Jensen on the degree sequence.
    --
    -- This requires:
    -- 1. A `homCount_of_leaf_decomposition` lemma (sum over `φ : H' →g G` of `G.degree (φ u)`).
    -- 2. A discrete Jensen inequality (`∑ x_i · w_i ≥ (∑ w_i) · ((∑ x_i w_i) / ∑ w_i)` with
    --    appropriate convexity).
    -- 3. Induction on `H.edgeFinset.card` (equivalently `|V| - 1`).
    --
    -- Deferred to a future commit; see `docs/PHASE2_PROOF_ROADMAP.md` §6.
    sorry

end SidorenkoConjecture
