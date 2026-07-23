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
# Written on the Wall II - Conjecture 59

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Counterexample

The conjecture is false. Take a bipartite chain graph `H` on `0, ..., 9` with parts
`{0, ..., 4}` and `{5, ..., 9}`, a universal hub `10` adjacent to every vertex of `H`, and
seven leaves `11, ..., 17` attached at the hub. This connected 18-vertex graph has
Havel–Hakimi residue `10`, largest induced bipartite subgraph of size `17`, and largest
induced forest of size `13`. Since `10 * 17 = 170 > 169 = 13 ^ 2`, we get
`⌈√(residue * b)⌉ = 14 > 13 = f`, violating the conjectured inequality.

The forest bound uses a pigeonhole argument: any `14`-vertex subset either contains the hub
together with six core vertices (two of which are adjacent, giving a triangle through the hub),
or omits the hub and contains seven core vertices (which always span a `4`-cycle).
-/

namespace WrittenOnTheWallII.GraphConjecture59

open Classical SimpleGraph

/-- Edges of the 10-vertex bipartite chain-graph core. -/
private def coreEdges : List (ℕ × ℕ) :=
  [(0, 5), (1, 5), (0, 6), (1, 6), (2, 6), (0, 7), (1, 7), (2, 7), (3, 7),
   (0, 8), (1, 8), (2, 8), (3, 8), (4, 8), (0, 9), (1, 9), (2, 9), (3, 9), (4, 9)]

/-- The 18-vertex counterexample described in the module docstring: the chain-graph core on
`0, ..., 9`, a universal hub `10`, and leaves `11, ..., 17` attached at the hub. -/
def counterexample : SimpleGraph (Fin 18) :=
  SimpleGraph.fromRel fun i j =>
    (i.val, j.val) ∈ coreEdges ∨
    (i.val ≤ 9 ∧ j.val = 10) ∨
    (i.val = 10 ∧ 11 ≤ j.val)

instance : DecidableRel counterexample.Adj := by
  unfold counterexample
  infer_instance

@[category test, AMS 5]
theorem counterexample_connected : counterexample.Connected := by
  native_decide

/-- The Havel–Hakimi residue of the counterexample is `10`. -/
@[category test, AMS 5]
theorem counterexample_residue : residue counterexample = 10 := by
  unfold residue
  decide +native

/- ### The two decidable core facts feeding the pigeonhole forest bound -/

/-- Any six core vertices contain an edge (the core has independence number `5`). -/
private lemma core_six_edge :
    ∀ t : Finset (Fin 18), (∀ v ∈ t, v.val ≤ 9) → 5 < t.card →
      ∃ u ∈ t, ∃ v ∈ t, counterexample.Adj u v := by
  native_decide

/-- Any seven core vertices span a `4`-cycle. -/
private lemma core_seven_c4 :
    ∀ t : Finset (Fin 18), (∀ v ∈ t, v.val ≤ 9) → 6 < t.card →
      ∃ a ∈ t, ∃ x ∈ t, ∃ c ∈ t, ∃ y ∈ t,
        counterexample.Adj a x ∧ counterexample.Adj x c ∧
        counterexample.Adj c y ∧ counterexample.Adj y a ∧ a ≠ c ∧ x ≠ y := by
  native_decide

/-- Every core vertex is adjacent to the hub. -/
private lemma core_adj_hub :
    ∀ v : Fin 18, v.val ≤ 9 → counterexample.Adj v ⟨10, by omega⟩ := by
  decide

/- ### Acyclicity obstructions via path uniqueness -/

/-- Two internally distinct two-edge paths between the same endpoints defeat acyclicity. -/
private lemma not_isAcyclic_of_two_paths {V : Type*} {G : SimpleGraph V} {a c x y : V}
    (hax : G.Adj a x) (hxc : G.Adj x c) (hay : G.Adj a y) (hyc : G.Adj y c)
    (hac : a ≠ c) (hxy : x ≠ y) : ¬ G.IsAcyclic := by
  intro hG
  have hpath := isAcyclic_iff_path_unique.mp hG
  have hp1 : (Walk.cons hax hxc.toWalk).IsPath := by
    simp [Walk.isPath_def, hax.ne, hxc.ne, hac]
  have hp2 : (Walk.cons hay hyc.toWalk).IsPath := by
    simp [Walk.isPath_def, hay.ne, hyc.ne, hac]
  have := hpath ⟨_, hp1⟩ ⟨_, hp2⟩
  have hsupp := congrArg (fun p : G.Path a c => p.1.support) this
  simp [Walk.support_cons] at hsupp
  exact hxy hsupp

/-- A triangle defeats acyclicity: the edge `a b` and the two-edge path through `h`
are distinct paths between `a` and `b`. -/
private lemma not_isAcyclic_of_triangle {V : Type*} {G : SimpleGraph V} {a b h : V}
    (hab : G.Adj a b) (hah : G.Adj a h) (hbh : G.Adj b h) : ¬ G.IsAcyclic := by
  intro hG
  have hpath := isAcyclic_iff_path_unique.mp hG
  have hp2 : (Walk.cons hah hbh.symm.toWalk).IsPath := by
    simp [Walk.isPath_def, hah.ne, hbh.ne', hab.ne]
  have := hpath (Path.singleton hab) ⟨_, hp2⟩
  have hlen := congrArg (fun p : G.Path a b => p.1.length) this
  simp [Path.singleton, Walk.length_cons] at hlen

/-- A graph in which every edge meets one fixed vertex is acyclic: around any cycle the
fixed vertex would have to occupy two distinct interior positions. -/
private lemma isAcyclic_of_all_edges_meet {V : Type*} {G : SimpleGraph V} (h : V)
    (hstar : ∀ ⦃u v : V⦄, G.Adj u v → u = h ∨ v = h) : G.IsAcyclic := by
  intro w c hc
  have hlen : 3 ≤ c.length := hc.three_le_length
  have hinj := hc.getVert_injOn
  have h01 : c.getVert 0 = h ∨ c.getVert 1 = h :=
    hstar (c.adj_getVert_succ (by omega))
  have h12 : c.getVert 1 = h ∨ c.getVert 2 = h :=
    hstar (c.adj_getVert_succ (by omega))
  have h23 : c.getVert 2 = h ∨ c.getVert 3 = h :=
    hstar (c.adj_getVert_succ (by omega))
  rcases h01 with h0 | h1
  · -- start at `h`: position 2 must also be `h`, but so is position `length`
    have h2 : c.getVert 2 = h := by
      rcases h12 with h1 | h2
      · have hadj := c.adj_getVert_succ (by omega : 0 < c.length)
        rw [h0, h1] at hadj
        exact (hadj.ne rfl).elim
      · exact h2
    have hL : c.getVert c.length = h := by
      rw [Walk.getVert_length]
      exact c.getVert_zero.symm.trans h0
    have : (2 : ℕ) = c.length := hinj (by simp; omega) (by simp; omega) (h2.trans hL.symm)
    omega
  · -- position 1 is `h`: position 3 must also be `h`
    have h2ne : c.getVert 2 ≠ h := fun h2 =>
      (c.adj_getVert_succ (by omega : 1 < c.length)).ne (h1.trans h2.symm)
    have h3 : c.getVert 3 = h := (h23.resolve_left h2ne)
    have : (1 : ℕ) = 3 := hinj (by simp; omega) (by simp; omega) (h1.trans h3.symm)
    omega

/- ### The forest number is 13 -/

set_option maxRecDepth 8192 in
/-- No subset with more than `13` vertices induces a forest. -/
@[category test, AMS 5]
theorem counterexample_no_forest_14 :
    ∀ s : Finset (Fin 18), 13 < s.card →
      ¬ (counterexample.induce (s : Set (Fin 18))).IsAcyclic := by
  intro s hcard hacyc
  classical
  -- count the core vertices inside `s`
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := s) (p := fun v : Fin 18 => v.val ≤ 9)
  have hnoncore : (s.filter fun v : Fin 18 => ¬ v.val ≤ 9).card ≤ 8 := by
    have hsub : (s.filter fun v : Fin 18 => ¬ v.val ≤ 9) ⊆
        (Finset.univ.filter fun v : Fin 18 => ¬ v.val ≤ 9) :=
      Finset.filter_subset_filter _ (Finset.subset_univ s)
    have h8 : (Finset.univ.filter fun v : Fin 18 => ¬ v.val ≤ 9).card = 8 := by decide
    exact le_of_le_of_eq (Finset.card_le_card hsub) h8
  by_cases hhubmem : (⟨10, by decide⟩ : Fin 18) ∈ s
  · -- hub present: six core vertices give an edge, hence a triangle through the hub
    have hcore : 5 < (s.filter fun v : Fin 18 => v.val ≤ 9).card := by omega
    obtain ⟨u, hu, v, hv, huv⟩ := core_six_edge _ (fun v hv => (Finset.mem_filter.mp hv).2) hcore
    have hu9 := (Finset.mem_filter.mp hu).2
    have hv9 := (Finset.mem_filter.mp hv).2
    have hus : u ∈ s := (Finset.mem_filter.mp hu).1
    have hvs : v ∈ s := (Finset.mem_filter.mp hv).1
    exact not_isAcyclic_of_triangle
      (a := (⟨u, hus⟩ : (s : Set (Fin 18)))) (b := ⟨v, hvs⟩)
      (h := ⟨⟨10, by decide⟩, hhubmem⟩)
      (by simpa using huv)
      (by simpa using core_adj_hub u hu9)
      (by simpa using core_adj_hub v hv9)
      hacyc
  · -- hub absent: seven core vertices give a 4-cycle
    have hcore : 6 < (s.filter fun v : Fin 18 => v.val ≤ 9).card := by
      -- the non-core part of `s` misses the hub, so it has at most 7 elements
      have h7le : (s.filter fun v : Fin 18 => ¬ v.val ≤ 9).card ≤ 7 := by
        have hsub : (s.filter fun v : Fin 18 => ¬ v.val ≤ 9) ⊆
            ((Finset.univ.filter fun v : Fin 18 => ¬ v.val ≤ 9).erase ⟨10, by decide⟩) := by
          intro w hw
          rcases Finset.mem_filter.mp hw with ⟨hws, hw9⟩
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw9⟩⟩
          rintro rfl
          exact hhubmem hws
        have h7 : (((Finset.univ.filter fun v : Fin 18 => ¬ v.val ≤ 9)).erase
            (⟨10, by decide⟩ : Fin 18)).card = 7 := by decide
        exact le_of_le_of_eq (Finset.card_le_card hsub) h7
      omega
    obtain ⟨a, ha, x, hx, c, hc, y, hy, hax, hxc, hcy, hya, hac, hxy⟩ :=
      core_seven_c4 _ (fun v hv => (Finset.mem_filter.mp hv).2) hcore
    have has : a ∈ s := (Finset.mem_filter.mp ha).1
    have hxs : x ∈ s := (Finset.mem_filter.mp hx).1
    have hcs : c ∈ s := (Finset.mem_filter.mp hc).1
    have hys : y ∈ s := (Finset.mem_filter.mp hy).1
    exact not_isAcyclic_of_two_paths
      (a := (⟨a, has⟩ : (s : Set (Fin 18)))) (c := ⟨c, hcs⟩) (x := ⟨x, hxs⟩) (y := ⟨y, hys⟩)
      (by simpa using hax) (by simpa using hxc)
      (by simpa using hya.symm) (by simpa using hcy.symm)
      (by simpa [Subtype.ext_iff] using hac) (by simpa [Subtype.ext_iff] using hxy)
      hacyc

/-- The `13`-vertex star `{5, ..., 9} ∪ {hub} ∪ {11, ..., 17}` induces a forest: every edge
of the induced subgraph goes through the hub, so two-edge fans through the hub are the only
cycles conceivable, and path uniqueness holds. -/
@[category test, AMS 5]
theorem counterexample_forest_13 :
    ∃ s : Finset (Fin 18),
      (counterexample.induce (s : Set (Fin 18))).IsAcyclic ∧ s.card = 13 := by
  classical
  refine ⟨({5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17} : Finset (Fin 18)), ?_, by decide⟩
  -- every edge of the induced subgraph meets the hub, and such graphs are acyclic
  refine isAcyclic_of_all_edges_meet
    (⟨⟨10, by omega⟩, by decide⟩ : (({5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17} :
      Finset (Fin 18)) : Set (Fin 18))) ?_
  native_decide

@[category test, AMS 5]
theorem counterexample_forest : counterexample.largestInducedForestSize = 13 := by
  unfold largestInducedForestSize
  apply le_antisymm
  · apply csSup_le
    · exact ⟨13, counterexample_forest_13.imp fun s h => ⟨h.1, h.2⟩⟩
    · rintro n ⟨s, hs, rfl⟩
      by_contra hlt
      push_neg at hlt
      exact counterexample_no_forest_14 s hlt hs
  · obtain ⟨s, hs, hcard⟩ := counterexample_forest_13
    exact le_csSup ⟨18, by rintro n ⟨t, -, rfl⟩; exact (Finset.card_le_univ t).trans (by simp)⟩
      ⟨s, hs, hcard⟩

/- ### The bipartite number is 17 -/

/-- The `17` vertices other than the hub induce a bipartite subgraph. -/
@[category test, AMS 5]
theorem counterexample_bipartite_17 :
    ∃ s : Finset (Fin 18),
      (counterexample.induce (s : Set (Fin 18))).IsBipartite ∧ s.card = 17 := by
  refine ⟨(Finset.univ.erase ⟨10, by omega⟩ : Finset (Fin 18)), ?_, by decide⟩
  exact ⟨SimpleGraph.Coloring.mk
    (fun v => if 5 ≤ (v : Fin 18).val ∧ (v : Fin 18).val ≤ 9 then (1 : Fin 2) else 0)
    (by native_decide)⟩

/-- No `18`-vertex subset induces a bipartite subgraph: the graph contains the triangle
`0, 5, 10`. -/
@[category test, AMS 5]
theorem counterexample_no_bipartite_18 :
    ∀ s : Finset (Fin 18),
      (counterexample.induce (s : Set (Fin 18))).IsBipartite → s.card ≤ 17 := by
  intro s hs
  by_contra h
  push_neg at h
  have hcard : s.card = 18 := le_antisymm (by simpa using s.card_le_univ) h
  have huniv : s = Finset.univ := s.eq_univ_of_card (by simpa using hcard)
  subst huniv
  rw [Finset.coe_univ] at hs
  have hG : counterexample.IsBipartite :=
    ⟨(Classical.choice hs).comp counterexample.induceUnivIso.symm.toHom⟩
  have h3 : ¬ counterexample.CliqueFree 3 := fun hcf =>
    hcf {0, 5, 10} (by constructor <;> native_decide)
  exact h3 (hG.cliqueFree (by norm_num))

@[category test, AMS 5]
theorem counterexample_b : b counterexample = 17 := by
  unfold b largestInducedBipartiteSubgraphSize
  norm_cast
  apply le_antisymm
  · apply csSup_le
    · exact ⟨17, counterexample_bipartite_17.imp fun s h => ⟨h.1, h.2⟩⟩
    · rintro n ⟨s, hs, rfl⟩
      exact counterexample_no_bipartite_18 s hs
  · obtain ⟨s, hs, hcard⟩ := counterexample_bipartite_17
    exact le_csSup ⟨18, by rintro n ⟨t, -, rfl⟩; exact (Finset.card_le_univ t).trans (by simp)⟩
      ⟨s, hs, hcard⟩

/--
WOWII [Conjecture 59](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$, the size $f(G)$ of a largest induced forest
satisfies $f(G) \ge \lceil \sqrt{\mathrm{residue}(G) \cdot b(G)} \rceil$, where
$\mathrm{residue}(G)$ is the Havel-Hakimi residue (the number of zeros remaining
after applying the Havel-Hakimi algorithm to the degree sequence until termination)
and $b(G)$ is the size of a largest induced bipartite subgraph.

See: Favaron, Mahéo, Saclé (1991) for the residue; DeLaVina's Graffiti.pc for the conjecture.

The answer is no, as witnessed by the 18-vertex graph described above: it has
residue `10`, `b = 17`, and largest induced forest `13`, while `⌈√170⌉ = 14`.
-/
@[category research solved, AMS 5]
theorem conjecture59 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_h : G.Connected),
      ⌈Real.sqrt ((residue G : ℝ) * b G)⌉ ≤ (G.largestInducedForestSize : ℝ) := by
  show False ↔ _
  rw [false_iff]
  intro h
  have hc := h (Fin 18) counterexample counterexample_connected
  rw [counterexample_residue, counterexample_b, counterexample_forest] at hc
  norm_cast at hc
  have h170 : (13 : ℝ) < Real.sqrt (((10 * 17 : ℕ) : ℝ)) := by
    rw [show (((10 * 17 : ℕ)) : ℝ) = 170 by norm_num, Real.lt_sqrt (by norm_num)]
    norm_num
  exact absurd hc (not_le.mpr (Int.lt_ceil.mpr (by exact_mod_cast h170)))

-- Sanity checks

/-- The `largestInducedForestSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.largestInducedForestSize := Nat.zero_le _

/-- The residue of $K_2$ equals $1$: degree sequence is $[1, 1]$; one Havel-Hakimi
step gives $[0]$, leaving a single zero. -/
@[category test, AMS 5]
example : residue (⊤ : SimpleGraph (Fin 2)) = 1 := by
  unfold residue; decide +native

end WrittenOnTheWallII.GraphConjecture59
