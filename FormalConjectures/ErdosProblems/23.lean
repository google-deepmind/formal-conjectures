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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 23

*References:*
* [erdosproblems.com/23](https://www.erdosproblems.com/23)
* [OEIS A389646](https://oeis.org/A389646)
* [Balogh-Clemen-Lidicky, Max Cuts in Triangle-free Graphs](https://arxiv.org/abs/2103.14179)
* [McKay, Extremal graphs for bipartization of triangle-free graphs](https://users.cecs.anu.edu.au/~bdm/data/graphs.html)
-/

@[expose] public section

open SimpleGraph BigOperators

namespace Erdos23

/-- The ten pairs of distinct vertices of `Fin 5`, in lexicographic order. -/
def n1_E : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

/-- The adjacency matrix of a graph on `Fin 5`, from its ten edge indicators. -/
def n1_A (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : Bool) : Fin 5 → Fin 5 → Bool :=
  ![![false, x01, x02, x03, x04], ![x01, false, x12, x13, x14], ![x02, x12, false, x23, x24],
    ![x03, x13, x23, false, x34], ![x04, x14, x24, x34, false]]

/-- Edge `i` is present in `A` and has both endpoints of the same colour under `c`. -/
def n1_bad (A : Fin 5 → Fin 5 → Bool) (c : Fin 5 → Bool) (i : Fin 10) : Bool :=
  A (n1_E i).1 (n1_E i).2 && (c (n1_E i).1 == c (n1_E i).2)

/-- Finite check: every triangle-free graph on `Fin 5` has a $2$-colouring with at most one
monochromatic edge. -/
@[category API, AMS 5]
theorem n1_fin : ∀ x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : Bool,
    (∀ a b c : Fin 5, n1_A x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 a b = true →
      n1_A x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 a c = true →
      n1_A x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 b c = true → False) →
    ∃ c0 c1 c2 c3 c4 : Bool, ∀ i j : Fin 10, i ≠ j →
      ¬ (n1_bad (n1_A x01 x02 x03 x04 x12 x13 x14 x23 x24 x34) ![c0, c1, c2, c3, c4] i = true ∧
         n1_bad (n1_A x01 x02 x03 x04 x12 x13 x14 x23 x24 x34) ![c0, c1, c2, c3, c4] j = true) := by
  decide +kernel

/-- Every pair of distinct vertices of `Fin 5` is one of the ten listed pairs. -/
@[category API, AMS 5]
theorem n1_cover : ∀ a b : Fin 5, a ≠ b → ∃ i : Fin 10,
    ((n1_E i).1 = a ∧ (n1_E i).2 = b) ∨ ((n1_E i).1 = b ∧ (n1_E i).2 = a) := by
  decide +kernel

open scoped Classical in
/--
Every triangle-free graph on $5$ vertices can be made bipartite by removing at most $1$ edge.
This is the $n = 1$ case of Erdős Problem 23.
-/
@[category test, AMS 5]
theorem erdos_23.variants.n1 :
    ∀ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin 5)),
        H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 1 := by
  intro G hG
  set A := n1_A (decide (G.Adj 0 1)) (decide (G.Adj 0 2)) (decide (G.Adj 0 3))
    (decide (G.Adj 0 4)) (decide (G.Adj 1 2)) (decide (G.Adj 1 3)) (decide (G.Adj 1 4))
    (decide (G.Adj 2 3)) (decide (G.Adj 2 4)) (decide (G.Adj 3 4)) with hAdef
  have hA : ∀ a b, A a b = decide (G.Adj a b) := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [hAdef, n1_A, G.adj_comm 1 0, G.adj_comm 2 0, G.adj_comm 3 0, G.adj_comm 4 0,
        G.adj_comm 2 1, G.adj_comm 3 1, G.adj_comm 4 1, G.adj_comm 3 2, G.adj_comm 4 2,
        G.adj_comm 4 3]
  obtain ⟨c0, c1, c2, c3, c4, hc⟩ := n1_fin _ _ _ _ _ _ _ _ _ _ (by
    intro a b c hab hac hbc
    rw [← hAdef, hA] at hab hac hbc
    exact hG {a, b, c} (is3Clique_triple_iff.2
      ⟨of_decide_eq_true hab, of_decide_eq_true hac, of_decide_eq_true hbc⟩))
  set col : Fin 5 → Bool := ![c0, c1, c2, c3, c4] with hcol
  let H : SimpleGraph (Fin 5) :=
    { Adj := fun a b => G.Adj a b ∧ col a ≠ col b
      symm := ⟨fun a b h => ⟨h.1.symm, h.2.symm⟩⟩
      loopless := ⟨fun a h => h.2 rfl⟩ }
  have hbad : ∀ a b, G.Adj a b → col a = col b → ∀ i : Fin 10,
      (((n1_E i).1 = a ∧ (n1_E i).2 = b) ∨ ((n1_E i).1 = b ∧ (n1_E i).2 = a)) →
      n1_bad A col i = true := by
    intro a b hab hcab i hi
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [n1_bad, hA, h1, h2, hab, hcab]
    · simp [n1_bad, hA, h1, h2, hab.symm, hcab]
  refine ⟨H, fun a b h => h.1, ?_, ?_⟩
  · exact (Coloring.mk (G := H) col (fun h => h.2)).colorable
  · refine Finset.card_le_one.2 ?_
    have key : ∀ e, e ∈ G.edgeSet → e ∉ H.edgeSet →
        ∃ a b, e = s(a, b) ∧ G.Adj a b ∧ col a = col b := by
      intro e he he'
      induction e using Sym2.ind with
      | _ a b =>
        simp only [mem_edgeSet] at he he'
        exact ⟨a, b, rfl, he, by simpa [H, he] using he'⟩
    intro e1 h1 e2 h2
    simp only [Finset.mem_sdiff, mem_edgeFinset] at h1 h2
    obtain ⟨a, b, rfl, hab, hcab⟩ := key _ h1.1 h1.2
    obtain ⟨k, l, rfl, hkl, hckl⟩ := key _ h2.1 h2.2
    obtain ⟨i, hi⟩ := n1_cover a b hab.ne
    obtain ⟨j, hj⟩ := n1_cover k l hkl.ne
    by_cases hij : i = j
    · subst hij
      rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hj with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
        simp [Sym2.eq_swap, ← h1, ← h2, ← h3, ← h4]
    · exact absurd ⟨hbad a b hab hcab i hi, hbad k l hkl hckl j hj⟩ (hc i j hij)

open scoped Classical in
/--
There exists a triangle-free graph on $5$ vertices such that at least $1$ edge must be removed
to make it bipartite. This shows the bound in `erdos_23_n1` is tight.
-/
@[category test, AMS 5]
theorem erdos_23.variants.n1_tight :
    ∃ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 ∧ ∀ (H : SimpleGraph (Fin 5)),
        H ≤ G → H.IsBipartite → 1 ≤ (G.edgeFinset \ H.edgeFinset).card := by
  -- The `5`-cycle is triangle-free, and a bipartite subgraph missing no edge would be the
  -- `5`-cycle itself, which has chromatic number `3`.
  refine ⟨cycleGraph 5, by unfold CliqueFree; decide +kernel, fun H hHG hH => ?_⟩
  by_contra hcon
  have h0 := Finset.card_eq_zero.1 (Nat.lt_one_iff.1 (not_le.1 hcon))
  have hsub := Finset.sdiff_eq_empty_iff_subset.1 h0
  rw [Finset.subset_iff] at hsub
  simp only [mem_edgeFinset] at hsub
  have hGH : cycleGraph 5 ≤ H := edgeSet_subset_edgeSet.1 fun _ he => hsub he
  obtain rfl : H = cycleGraph 5 := le_antisymm hHG hGH
  have h2 := hH.chromaticNumber_le
  rw [chromaticNumber_cycleGraph_of_odd 5 (by norm_num) (by decide)] at h2
  exact absurd h2 (by decide)

open scoped Classical in
/--
Every triangle-free graph on $25$ vertices can be made bipartite by removing at most $25$
edges.

This is the $n = 5$ case of Erdős Problem 23.  It follows from the high-density range of
Balogh-Clemen-Lidicky together with McKay's complete catalogue of the 23-vertex extremal
graphs for bipartization of triangle-free graphs.
-/
@[category research solved, AMS 5]
theorem erdos_23.variants.n5 :
    ∀ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin 25)),
        H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 25 := by
  sorry

/--
The blow-up of the 5-cycle $C_5$: replace each vertex of $C_5$ with an independent set of $n$
vertices, and connect two vertices iff their corresponding vertices in $C_5$ are adjacent.
The vertex set is $\mathbb{Z}/5\mathbb{Z} \times \{0, \ldots, n-1\}$, where $(i, a)$ and $(j, b)$
are adjacent iff $j = i + 1$ or $i = j + 1$ in $\mathbb{Z}/5\mathbb{Z}$.
-/
def blowupC5 (n : ℕ) : SimpleGraph (ZMod 5 × Fin n) :=
  SimpleGraph.fromRel fun (i, _) (j, _) => i + 1 = j ∨ j + 1 = i

/-- The blow-up of $C_5$ is triangle-free: three vertices would need pairwise cyclically
adjacent parts in $\mathbb{Z}/5\mathbb{Z}$. -/
@[category test, AMS 5]
theorem blowupC5_cliqueFree (n : ℕ) : (blowupC5 n).CliqueFree 3 := by
  intro s hs
  obtain ⟨⟨i, a⟩, ⟨j, b⟩, ⟨k, c⟩, hab, hac, hbc, -⟩ := is3Clique_iff.1 hs
  simp only [blowupC5, fromRel_adj] at hab hac hbc
  have key : ∀ x y z : ZMod 5, (x + 1 = y ∨ y + 1 = x) → (x + 1 = z ∨ z + 1 = x) →
      (y + 1 = z ∨ z + 1 = y) → False := by decide
  exact key i j k (by tauto) (by tauto) (by tauto)

/-- The edge of the blow-up joining the vertices over `i` and `i + 1` of a transversal `f`. -/
def blowupC5_edge {n : ℕ} (f : ZMod 5 → Fin n) (i : ZMod 5) : Sym2 (ZMod 5 × Fin n) :=
  s((i, f i), (i + 1, f (i + 1)))

@[category API, AMS 5]
lemma blowupC5_adj {n : ℕ} (f : ZMod 5 → Fin n) (i : ZMod 5) :
    (blowupC5 n).Adj (i, f i) (i + 1, f (i + 1)) := by
  rw [blowupC5, SimpleGraph.fromRel_adj]
  refine ⟨fun h => ?_, by simp⟩
  exact (by decide : ∀ i : ZMod 5, i ≠ i + 1) i (congrArg Prod.fst h)

/-- A bipartite graph cannot contain all five edges of a transversal cycle. -/
@[category API, AMS 5]
lemma blowupC5_not_all_adj {n : ℕ} (H : SimpleGraph (ZMod 5 × Fin n)) (hBip : H.IsBipartite)
    (f : ZMod 5 → Fin n) : ∃ i : ZMod 5, ¬ H.Adj (i, f i) (i + 1, f (i + 1)) := by
  obtain ⟨c⟩ := hBip
  by_contra hall
  have hall' : ∀ i : ZMod 5, H.Adj (i, f i) (i + 1, f (i + 1)) :=
    fun i => by_contra fun h => hall ⟨i, h⟩
  have key : ∀ g : ZMod 5 → Fin 2, ¬ ∀ i, g i ≠ g (i + 1) := by decide
  exact key (fun i => c (i, f i)) fun i => c.valid (hall' i)

@[category API, AMS 5]
lemma blowupC5_edge_eq {n : ℕ} {f g : ZMod 5 → Fin n} {i j : ZMod 5}
    (h : blowupC5_edge f i = blowupC5_edge g j) :
    j = i ∧ f i = g i ∧ f (i + 1) = g (i + 1) := by
  unfold blowupC5_edge at h
  rw [Sym2.eq_iff] at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩
  · subst h1
    exact ⟨rfl, h2, h4⟩
  · exact absurd h3 (fun h3 => (by decide : ∀ i j : ZMod 5, i = j + 1 → i + 1 = j → False)
      i j h1 h3)

/-- The pairs (transversal, index) whose edge is `d`. -/
def blowupC5_fiber (n : ℕ) (d : Sym2 (ZMod 5 × Fin n)) : Finset ((ZMod 5 → Fin n) × ZMod 5) :=
  Finset.univ.filter fun p => blowupC5_edge p.1 p.2 = d

@[category API, AMS 5]
lemma blowupC5_mem_fiber {n : ℕ} {d : Sym2 (ZMod 5 × Fin n)} {p : (ZMod 5 → Fin n) × ZMod 5} :
    p ∈ blowupC5_fiber n d ↔ blowupC5_edge p.1 p.2 = d := by
  simp [blowupC5_fiber]

@[category API, AMS 5]
lemma blowupC5_fiber_card (n : ℕ) (d : Sym2 (ZMod 5 × Fin n)) :
    (blowupC5_fiber n d).card ≤ n ^ 3 := by
  rcases (blowupC5_fiber n d).eq_empty_or_nonempty with h | ⟨p0, hp0⟩
  · simp [h]
  set s : Finset (ZMod 5) := ({p0.2, p0.2 + 1} : Finset (ZMod 5))ᶜ with hs
  have hscard : s.card = 3 := by
    have hne : p0.2 ≠ p0.2 + 1 := (by decide : ∀ i : ZMod 5, i ≠ i + 1) _
    rw [hs, Finset.card_compl, Finset.card_pair hne, ZMod.card]
  have hinj : Set.InjOn (fun p : (ZMod 5 → Fin n) × ZMod 5 => fun x : s => p.1 x)
      (blowupC5_fiber n d) := by
    intro p hp q hq hpq
    have e0 := (blowupC5_mem_fiber.1 hp0)
    obtain ⟨hp2, hpa, hpb⟩ := blowupC5_edge_eq ((blowupC5_mem_fiber.1 hp).trans e0.symm)
    obtain ⟨hq2, hqa, hqb⟩ := blowupC5_edge_eq ((blowupC5_mem_fiber.1 hq).trans e0.symm)
    refine Prod.ext (funext fun x => ?_) (hp2.symm.trans hq2)
    by_cases hx : x ∈ s
    · exact congrFun hpq ⟨x, hx⟩
    · rw [← hp2] at hpa hpb
      rw [← hq2] at hqa hqb
      simp only [hs, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_not] at hx
      rcases hx with rfl | rfl
      · exact hpa.trans hqa.symm
      · exact hpb.trans hqb.symm
  calc (blowupC5_fiber n d).card
      ≤ (Finset.univ : Finset (s → Fin n)).card :=
        Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
    _ = n ^ 3 := by simp [hscard]

open scoped Classical in
/--
The blow-up of $C_5$ shows that the bound $n^2$ in Erdős Problem 23 is tight:
any bipartite subgraph must omit at least $n^2$ edges.
-/
@[category test, AMS 5]
theorem blowupC5_tight (n : ℕ) (_hn : 0 < n) (H : SimpleGraph (ZMod 5 × Fin n))
    (hH : H ≤ blowupC5 n) (hBip : H.IsBipartite) :
    n ^ 2 ≤ ((blowupC5 n).edgeFinset \ H.edgeFinset).card := by
  have _ := hH  -- the argument `hH` is not needed: only edges of `H` lying in `blowupC5 n` are used
  set D := (blowupC5 n).edgeFinset \ H.edgeFinset with hD
  have hex : ∀ f : ZMod 5 → Fin n, ∃ i, blowupC5_edge f i ∈ D := by
    intro f
    obtain ⟨i, hi⟩ := blowupC5_not_all_adj H hBip f
    refine ⟨i, ?_⟩
    simp only [hD, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, blowupC5_edge,
      SimpleGraph.mem_edgeSet]
    exact ⟨blowupC5_adj f i, hi⟩
  choose g hg using hex
  have hlow : n ^ 5 ≤ (D.biUnion (blowupC5_fiber n)).card := by
    have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (ZMod 5 → Fin n)))
      (t := D.biUnion (blowupC5_fiber n)) (fun f => (f, g f))
      (fun f _ => Finset.mem_coe.2 (Finset.mem_biUnion.2
        ⟨_, hg f, blowupC5_mem_fiber.2 rfl⟩))
      (fun f _ f' _ h => congrArg Prod.fst h)
    simpa using h
  have hup : (D.biUnion (blowupC5_fiber n)).card ≤ D.card * n ^ 3 :=
    Finset.card_biUnion_le.trans
      (Finset.sum_le_card_nsmul _ _ _ fun d _ => blowupC5_fiber_card n d)
  have h5 : n ^ 2 * n ^ 3 ≤ D.card * n ^ 3 := by
    rw [← pow_add]
    exact hlow.trans hup
  exact Nat.le_of_mul_le_mul_right h5 (pow_pos _hn 3)

open scoped Classical in
/--
There exists a triangle-free graph on $25$ vertices such that at least $25$ edges must be
removed to make it bipartite.  The balanced blow-up of $C_5$ with five parts of size $5$
witnesses this.
-/
@[category research solved, AMS 5]
theorem erdos_23.variants.n5_tight :
    ∃ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 ∧ ∀ (H : SimpleGraph (Fin 25)),
        H ≤ G → H.IsBipartite → 25 ≤ (G.edgeFinset \ H.edgeFinset).card := by
  obtain ⟨e⟩ : Nonempty (Fin 25 ≃ ZMod 5 × Fin 5) :=
    ⟨Fintype.equivOfCardEq (by simp)⟩
  refine ⟨(blowupC5 5).comap e,
    (blowupC5_cliqueFree 5).comap ⟨(SimpleGraph.Iso.comap e _).toEmbedding.toCopy⟩,
    fun H hle hH => ?_⟩
  obtain ⟨C⟩ := hH
  -- `H'` is the image of `H` in the blow-up; it is bipartite and lies inside the blow-up.
  let H' : SimpleGraph (ZMod 5 × Fin 5) := H.comap e.symm
  have hle' : H' ≤ blowupC5 5 := fun a b hab => by simpa using hle hab
  have hbip : H'.IsBipartite := ⟨Coloring.mk (fun a => C (e.symm a)) fun hab => C.valid hab⟩
  refine ((by norm_num : (25 : ℕ) = 5 ^ 2).trans_le
    (blowupC5_tight 5 (by norm_num) H' hle' hbip)).trans ?_
  refine Finset.card_le_card_of_injOn (Sym2.map e.symm) ?_
    (Sym2.map.injective e.symm.injective).injOn
  intro s hs
  induction s using Sym2.ind with
  | _ a b =>
    simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, mem_edgeFinset, mem_edgeSet] at hs ⊢
    simpa [H', Sym2.map_mk] using hs

open scoped Classical in
/--
Can every triangle-free graph on $5n$ vertices be made bipartite by deleting at most $n^2$ edges?
-/
@[category research open, AMS 5]
theorem erdos_23 : answer(sorry) ↔
    ∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
      ∀ (G : SimpleGraph V), G.CliqueFree 3 →
        ∃ (H : SimpleGraph V),
          H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ n^2 := by
  sorry

-- TODO: add the remaining variants/statements/comments

end Erdos23
