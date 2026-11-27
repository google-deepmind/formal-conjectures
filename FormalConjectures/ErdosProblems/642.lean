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
# Erdős Problem 642

*References:*
- [erdosproblems.com/642](https://www.erdosproblems.com/642)
- [CES96] Chen, Guantao and Erdős, Paul and Staton, William, *Proof of a conjecture of Bollobás
  on nested cycles*. J. Combin. Theory Ser. B (1996), 38--43.
- [DMMS24] Draganić, Nemanja and Methuku, Abhishek and Munhá Correia, David and Sudakov,
  Benny, *Cycles with many chords*. Random Structures Algorithms (2024), 3--16.
- [Er97d] Erdős, Paul, *Some recent problems and results in graph theory*. Discrete Math.
  (1997), 81-85.
-/

@[expose] public section

open Filter

namespace Erdos642

/-- Every cycle of the graph `G` has more vertices than chords.

A cycle is a closed walk `c` with `c.IsCycle`. It has `c.length` vertices. A chord of `c` is an
edge of `G` between two vertices of `c` that is not an edge of `c`
(`SimpleGraph.Walk.IsChord`). -/
def CyclesHaveMoreVerticesThanChords {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (c : G.Walk v v), c.IsCycle → {e : Sym2 V | c.IsChord e}.ncard < c.length

open scoped Classical in
/-- The maximal number $f(n)$ of edges of a graph on `n` vertices in which every cycle has more
vertices than chords. There are finitely many graphs on `Fin n`, so the supremum is a maximum. -/
noncomputable def maxEdges (n : ℕ) : ℕ :=
  (Finset.univ.filter fun G : SimpleGraph (Fin n) => CyclesHaveMoreVerticesThanChords G).sup
    fun G => G.edgeSet.ncard

/--
Let $f(n)$ be the maximal number of edges in a graph on $n$ vertices such that all cycles have more
vertices than chords. Is it true that $f(n)\ll n$?

A problem of Hamburger and Szegedy. A chord is an edge between two vertices of the cycle which are
not consecutive in the cycle.
-/
@[category research open, question, AMS 5]
theorem erdos_642 :
    (fun n : ℕ => (maxEdges n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  sorry

/-- Chen, Erdős, and Staton [CES96] proved $f(n) \ll n^{3/2}$. -/
@[category research solved, AMS 5]
theorem erdos_642.variants.upper_bound_n_pow_three_halves :
    (fun n : ℕ => (maxEdges n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) := by
  sorry

/--
Draganić, Methuku, Munhá Correia, and Sudakov [DMMS24] have improved this to
$$f(n) \ll n(\log n)^8.$$
-/
@[category research solved, AMS 5]
theorem erdos_642.variants.upper_bound_n_log_pow_eight :
    (fun n : ℕ => (maxEdges n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) * Real.log n ^ 8) := by
  sorry

/-- A graph without cycles satisfies the condition, since there is no cycle to check. -/
@[category test, AMS 5]
theorem cyclesHaveMoreVerticesThanChords_of_isAcyclic {V : Type*} {G : SimpleGraph V}
    (hG : G.IsAcyclic) : CyclesHaveMoreVerticesThanChords G :=
  fun _ c hc => absurd hc (hG c)

open scoped Classical in
/-- Every graph on `n` vertices in which every cycle has more vertices than chords has at most
`maxEdges n` edges. -/
@[category API, AMS 5]
theorem le_maxEdges {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : CyclesHaveMoreVerticesThanChords G) : G.edgeSet.ncard ≤ maxEdges n := by
  unfold maxEdges
  exact Finset.le_sup (f := fun H : SimpleGraph (Fin n) => H.edgeSet.ncard)
    (Finset.mem_filter.2 ⟨Finset.mem_univ G, hG⟩)

/-- The maximum defining $f(n)$ is attained by an admissible graph. -/
@[category API, AMS 5]
theorem exists_maxEdges (n : ℕ) :
    ∃ G : SimpleGraph (Fin n), CyclesHaveMoreVerticesThanChords G ∧
      G.edgeSet.ncard = maxEdges n := by
  classical
  have hne : (Finset.univ.filter fun G : SimpleGraph (Fin n) =>
      CyclesHaveMoreVerticesThanChords G).Nonempty := by
    refine ⟨⊥, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    exact cyclesHaveMoreVerticesThanChords_of_isAcyclic SimpleGraph.isAcyclic_bot
  obtain ⟨G, hG, hmax⟩ := Finset.exists_mem_eq_sup _ hne (fun G => G.edgeSet.ncard)
  exact ⟨G, (Finset.mem_filter.1 hG).2, hmax.symm⟩

/-- The elementary bound $f(n)\leq\binom n2$. -/
@[category API, AMS 5]
theorem maxEdges_le_choose_two (n : ℕ) : maxEdges n ≤ n.choose 2 := by
  classical
  obtain ⟨G, _, hG⟩ := exists_maxEdges n
  rw [← hG]
  simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card', Fintype.card_fin] using
    G.card_edgeFinset_le_card_choose_two

/-- There are no edges on an empty vertex set. -/
@[category test, AMS 5]
theorem maxEdges_zero : maxEdges 0 = 0 := by
  have := maxEdges_le_choose_two 0
  simpa using this

/-- In any finite graph, the number of chords of a cycle plus its length is at most the total
number of edges of the graph. -/
@[category API, AMS 5]
theorem ncard_isChord_add_length_le_ncard_edgeSet {V : Type*} [Fintype V]
    {G : SimpleGraph V} {v : V} {c : G.Walk v v} (hc : c.IsCycle) :
    {e : Sym2 V | c.IsChord e}.ncard + c.length ≤ G.edgeSet.ncard := by
  classical
  have hsub : {e : Sym2 V | c.IsChord e} ∪ {e : Sym2 V | e ∈ c.edges} ⊆ G.edgeSet := by
    rintro e (he | he)
    · exact he.1
    · exact c.edges_subset_edgeSet he
  have hdisj : Disjoint {e : Sym2 V | c.IsChord e} {e : Sym2 V | e ∈ c.edges} :=
    Set.disjoint_left.2 fun _ he hmem ↦ he.2.1 hmem
  have hcedges : {e : Sym2 V | e ∈ c.edges}.ncard = c.length := by
    have hcoe : (c.edges.toFinset : Set (Sym2 V)) = {e : Sym2 V | e ∈ c.edges} := by ext; simp
    rw [← hcoe, Set.ncard_coe_finset, List.toFinset_card_of_nodup hc.edges_nodup, c.length_edges]
  rw [← hcedges, ← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

/-- For any cycle `c`, the number of chords of `c` plus `c.length` is at most
`(c.length).choose 2`. -/
@[category API, AMS 5]
theorem ncard_isChord_add_length_le_choose_two {V : Type*} {G : SimpleGraph V}
    {v : V} {c : G.Walk v v} (hc : c.IsCycle) :
    {e : Sym2 V | c.IsChord e}.ncard + c.length ≤ c.length.choose 2 := by
  classical
  have hmem_tail : ∀ w ∈ c.support, w ∈ c.support.tail := by
    cases c with
    | nil => exact absurd SimpleGraph.Walk.Nil.nil hc.not_nil
    | cons _ p =>
      intro w hw
      simp only [SimpleGraph.Walk.support_cons, List.tail_cons, List.mem_cons] at hw ⊢
      rcases hw with rfl | hw
      · exact p.end_mem_support
      · exact hw
  let S : Finset V := c.support.tail.toFinset
  have hScard : S.card = c.length := by
    rw [List.toFinset_card_of_nodup hc.support_nodup]
    cases c with
    | nil => exact absurd SimpleGraph.Walk.Nil.nil hc.not_nil
    | cons _ p => simp [SimpleGraph.Walk.length_support]
  let E : Finset (Sym2 V) := (⊤ : SimpleGraph S).edgeFinset.image (Sym2.map Subtype.val)
  have hsub : {e : Sym2 V | c.IsChord e} ∪ {e : Sym2 V | e ∈ c.edges} ⊆ (E : Set (Sym2 V)) := by
    intro e he
    have hGe : e ∈ G.edgeSet ∧ ∀ a b, e = s(a, b) → a ∈ S ∧ b ∈ S := by
      rcases he with hc_e | hm_e
      · refine ⟨hc_e.1, fun a b hab ↦ ?_⟩
        subst hab
        change c.IsChord s(a, b) at hc_e
        rw [SimpleGraph.Walk.isChord_sym2Mk] at hc_e
        exact ⟨ List.mem_toFinset.2 (hmem_tail a hc_e.2.2.1),
                List.mem_toFinset.2 (hmem_tail b hc_e.2.2.2) ⟩
      · refine ⟨c.edges_subset_edgeSet hm_e, fun a b hab ↦ ?_⟩
        subst hab
        exact ⟨ List.mem_toFinset.2 (hmem_tail a (c.fst_mem_support_of_mem_edges hm_e)),
                List.mem_toFinset.2 (hmem_tail b (c.snd_mem_support_of_mem_edges hm_e)) ⟩
    induction e using Sym2.ind with
    | h a b =>
      obtain ⟨ha, hb⟩ := hGe.2 a b rfl
      have hne : (⟨a, ha⟩ : S) ≠ ⟨b, hb⟩ := by
        intro h
        exact (G.mem_edgeSet.1 hGe.1).ne (congrArg Subtype.val h)
      exact Finset.mem_coe.2 (Finset.mem_image.2
        ⟨s(⟨a, ha⟩, ⟨b, hb⟩), SimpleGraph.mem_edgeFinset.2 hne, rfl⟩)
  have hfinC : {e : Sym2 V | c.IsChord e}.Finite :=
    E.finite_toSet.subset (Set.subset_union_left.trans hsub)
  have hfinE : {e : Sym2 V | e ∈ c.edges}.Finite :=
    E.finite_toSet.subset (Set.subset_union_right.trans hsub)
  have hdisj : Disjoint {e : Sym2 V | c.IsChord e} {e : Sym2 V | e ∈ c.edges} :=
    Set.disjoint_left.2 fun _ he hmem ↦ he.2.1 hmem
  have hcedges : {e : Sym2 V | e ∈ c.edges}.ncard = c.length := by
    have hcoe : (c.edges.toFinset : Set (Sym2 V)) = {e : Sym2 V | e ∈ c.edges} := by ext; simp
    rw [← hcoe, Set.ncard_coe_finset, List.toFinset_card_of_nodup hc.edges_nodup, c.length_edges]
  calc
    {e : Sym2 V | c.IsChord e}.ncard + c.length
      = ({e : Sym2 V | c.IsChord e} ∪ {e : Sym2 V | e ∈ c.edges}).ncard := by
          rw [Set.ncard_union_eq hdisj hfinC hfinE, hcedges]
    _ ≤ (E : Set (Sym2 V)).ncard := Set.ncard_le_ncard hsub E.finite_toSet
    _ = E.card := Set.ncard_coe_finset E
    _ ≤ (⊤ : SimpleGraph S).edgeFinset.card := Finset.card_image_le
    _ = c.length.choose 2 := by
          rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_coe, hScard]

/-- Every cycle of length at most `4` has strictly fewer chords than vertices. -/
@[category API, AMS 5]
theorem ncard_isChord_lt_of_length_le_four {V : Type*} {G : SimpleGraph V}
    {v : V} {c : G.Walk v v} (hc : c.IsCycle) (hlen : c.length ≤ 4) :
    {e : Sym2 V | c.IsChord e}.ncard < c.length := by
  have h3 := hc.three_le_length
  have hbound := ncard_isChord_add_length_le_choose_two hc
  have h32 : Nat.choose 3 2 = 3 := by decide
  have h42 : Nat.choose 4 2 = 6 := by decide
  interval_cases c.length <;> omega

/-- Every graph on at most `4` vertices satisfies `CyclesHaveMoreVerticesThanChords`. -/
@[category API, AMS 5]
theorem cyclesHaveMoreVerticesThanChords_of_card_le_four {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hV : Fintype.card V ≤ 4) :
    CyclesHaveMoreVerticesThanChords G := by
  classical
  intro v c hc
  have hlen : c.length ≤ Fintype.card V := by
    have h1 : c.support.tail.length = c.length := by
      cases c with
      | nil => exact absurd SimpleGraph.Walk.Nil.nil hc.not_nil
      | cons _ p => simp [SimpleGraph.Walk.length_support]
    rw [← h1, ← List.toFinset_card_of_nodup hc.support_nodup]
    exact Finset.card_le_univ _
  exact ncard_isChord_lt_of_length_le_four hc (hlen.trans hV)

/-- For `n ≤ 4`, the complete graph is admissible, so $f(n) = \binom{n}{2}$
(giving $f(0) = 0$, $f(1) = 0$, $f(2) = 1$, $f(3) = 3$, and $f(4) = 6$). -/
@[category test, AMS 5]
theorem maxEdges_eq_choose_two_of_le_four {n : ℕ} (hn : n ≤ 4) :
    maxEdges n = n.choose 2 := by
  refine le_antisymm (maxEdges_le_choose_two n) ?_
  have htop : CyclesHaveMoreVerticesThanChords (⊤ : SimpleGraph (Fin n)) :=
    cyclesHaveMoreVerticesThanChords_of_card_le_four _ (by simpa using hn)
  have hcard : (⊤ : SimpleGraph (Fin n)).edgeSet.ncard = n.choose 2 := by
    simpa [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n)
  exact hcard ▸ le_maxEdges ⊤ htop

/-- For `n = 5`, $K_5$ fails on a Hamiltonian $5$-cycle ($5$ chords) while $K_5 - e$ is admissible,
so $f(5) = 9$. -/
@[category test, AMS 5]
theorem maxEdges_five : maxEdges 5 = 9 := by
  classical
  have h52 : Nat.choose 5 2 = 10 := by decide
  have htop10 : (⊤ : SimpleGraph (Fin 5)).edgeSet.ncard = 10 := by
    have := SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin 5)
    simpa [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card', h52] using this
  refine le_antisymm ?_ ?_
  · obtain ⟨G, hG, hmax⟩ := exists_maxEdges 5
    rw [← hmax]
    by_contra! hgt
    have hle10 : G.edgeSet.ncard ≤ 10 := by
      have := G.card_edgeFinset_le_card_choose_two
      simpa [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card', h52] using this
    have heq10 : G.edgeFinset.card = (⊤ : SimpleGraph (Fin 5)).edgeFinset.card := by
      have h1 : G.edgeFinset.card = G.edgeSet.ncard :=
        (Set.ncard_eq_toFinset_card' G.edgeSet).symm
      have h2 : (⊤ : SimpleGraph (Fin 5)).edgeFinset.card = 10 := by
        simpa [h52] using SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin 5)
      omega
    have hGtop : G = ⊤ := SimpleGraph.edgeFinset_inj.1 <|
      Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono le_top) heq10.ge
    subst hGtop
    let c : (⊤ : SimpleGraph (Fin 5)).Walk 0 0 := (SimpleGraph.cycleGraph.cycle 2).mapLe le_top
    have hc : c.IsCycle := SimpleGraph.cycleGraph.isCycle_cycle.mapLe le_top
    have hclen : c.length = 5 := by simp [c]
    have htail_card : c.support.tail.toFinset.card = (Finset.univ : Finset (Fin 5)).card := by
      rw [List.toFinset_card_of_nodup hc.support_nodup, Finset.card_univ, Fintype.card_fin]
      cases heq : c with
      | nil => exact absurd (heq ▸ SimpleGraph.Walk.Nil.nil) hc.not_nil
      | cons _ p =>
        have := congrArg SimpleGraph.Walk.length heq
        simpa [SimpleGraph.Walk.length_support, hclen] using this
    have huniv : c.support.tail.toFinset = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ _) htail_card.ge
    have hmem_all : ∀ w : Fin 5, w ∈ c.support := fun w ↦
      List.mem_of_mem_tail (List.mem_toFinset.1 (huniv ▸ Finset.mem_univ w))
    have hunion : {e : Sym2 (Fin 5) | c.IsChord e} ∪ {e : Sym2 (Fin 5) | e ∈ c.edges} =
        (⊤ : SimpleGraph (Fin 5)).edgeSet := by
      ext e
      constructor
      · rintro (he | he)
        · exact he.1
        · exact c.edges_subset_edgeSet he
      · intro he
        by_cases hm : e ∈ c.edges
        · exact Or.inr hm
        · refine Or.inl ⟨he, hm, ?_⟩
          induction e using Sym2.ind with
          | h a b => exact ⟨hmem_all a, hmem_all b⟩
    have hdisj : Disjoint {e : Sym2 (Fin 5) | c.IsChord e} {e : Sym2 (Fin 5) | e ∈ c.edges} :=
      Set.disjoint_left.2 fun _ he hmem ↦ he.2.1 hmem
    have hcedges : {e : Sym2 (Fin 5) | e ∈ c.edges}.ncard = 5 := by
      have hcoe : (c.edges.toFinset : Set (Sym2 (Fin 5))) = {e : Sym2 (Fin 5) | e ∈ c.edges} := by
        ext; simp
      rw [← hcoe, Set.ncard_coe_finset, List.toFinset_card_of_nodup hc.edges_nodup,
        c.length_edges, hclen]
    have hsum := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
    rw [hunion, htop10, hcedges] at hsum
    have hlt := hG 0 c hc
    omega
  · let G₅ : SimpleGraph (Fin 5) := (⊤ : SimpleGraph (Fin 5)).deleteEdges {s(0, 1)}
    have h9 : G₅.edgeSet.ncard = 9 := by
      have hmem01 : s((0 : Fin 5), 1) ∈ (⊤ : SimpleGraph (Fin 5)).edgeSet := by decide
      rw [SimpleGraph.edgeSet_deleteEdges, Set.ncard_sdiff_singleton_of_mem hmem01, htop10]
    have hG₅ : CyclesHaveMoreVerticesThanChords G₅ := by
      intro v c hc
      by_cases hlen4 : c.length ≤ 4
      · exact ncard_isChord_lt_of_length_le_four hc hlen4
      · have hle5 : c.length ≤ 5 := by
          have h1 : c.support.tail.length = c.length := by
            cases c with
            | nil => exact absurd SimpleGraph.Walk.Nil.nil hc.not_nil
            | cons _ p => simp [SimpleGraph.Walk.length_support]
          rw [← h1, ← List.toFinset_card_of_nodup hc.support_nodup]
          exact (Finset.card_le_univ _).trans (by simp)
        have hsum := ncard_isChord_add_length_le_ncard_edgeSet hc
        omega
    exact h9 ▸ le_maxEdges G₅ hG₅

/-- The asymptotic question is equivalent to a uniform linear edge bound for every admissible
finite graph, including the empty graph. -/
@[category API, AMS 5]
theorem isBigO_iff_uniform_edge_bound :
    ((fun n : ℕ => (maxEdges n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ))) ↔
      ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        CyclesHaveMoreVerticesThanChords G → (G.edgeSet.ncard : ℝ) ≤ C * n := by
  have hzero : ∀ n : ℕ, (n : ℝ) = 0 → (maxEdges n : ℝ) = 0 := by
    intro n hn
    have : n = 0 := by exact_mod_cast hn
    simp [this, maxEdges_zero]
  rw [Asymptotics.isBigO_nat_atTop_iff hzero]
  simp only [Real.norm_natCast]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun n G hG => ?_⟩
    exact (Nat.cast_le.2 (le_maxEdges G hG)).trans (hC n)
  · rintro ⟨C, hC⟩
    refine ⟨C, fun n => ?_⟩
    obtain ⟨G, hG, hmax⟩ := exists_maxEdges n
    simpa [hmax] using hC n G hG

end Erdos642
