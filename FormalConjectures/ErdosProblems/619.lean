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
# Erdős Problem 619

*References:*
- [erdosproblems.com/619](https://www.erdosproblems.com/619)
- [EGR98] Erdős, Paul and Gyárfás, András and Ruszinkó, Miklós, *How to decrease the
  diameter of triangle-free graphs*. Combinatorica **18** (1998), 493-501.
- [Er99] Erdős, Paul, *A selection of problems and results in combinatorics*.
  Combin. Probab. Comput. **8** (1999), 1-6.
-/

open SimpleGraph

namespace Erdos619

/--
For a graph $G$, `minNewEdges r G` is the smallest number of edges that need to be added
to $G$ so that it has diameter at most $r$, while preserving the property of being
triangle-free. Erdős, Gyárfás and Ruszinkó denote this quantity by $h_r(G)$ in [EGR98].

Adding edges is formalised as passing to a supergraph `H ≥ G` on the same vertex set, the
number of added edges being the (finite) cardinality of the edge set of `H \ G`. We use
the extended diameter `SimpleGraph.ediam` (valued in `ℕ∞`) so that disconnected
supergraphs, which have infinite diameter, do not qualify. If no triangle-free supergraph
of `G` of diameter at most `r` exists, then `minNewEdges r G = 0` by the `Nat.sInf`
convention on the empty set; `erdos_619.variants.add_edges_diam_three` shows this
degenerate case does not occur for connected triangle-free `G` when `3 ≤ r`.
-/
noncomputable def minNewEdges {V : Type*} (r : ℕ) (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ H : SimpleGraph V,
    G ≤ H ∧ H.CliqueFree 3 ∧ H.ediam ≤ r ∧ (H \ G).edgeSet.ncard = k}

set_option linter.style.category_attribute false
set_option linter.style.ams_attribute false

open scoped BigOperators

/-
## Inline disproof machinery

The declarations in this section are the self-contained counterexample proof and the
bridge from its `IsHR` formulation to `minNewEdges`.
-/

namespace Disproof

noncomputable section

/-- The number of new edges in `H` that were not already present in `G`. -/
def addedEdgeCount {n : ℕ} (G H : SimpleGraph (Fin n)) : ℕ :=
  (H.edgeFinset \ G.edgeFinset).card

/-- `IsHR r G m` says that `m` is the value of `h_r(G)`: it is achieved by a
triangle-free supergraph of `G` with extended diameter at most `r`, and is minimal among all such
supergraphs.

Using `ediam` avoids the junk value of `diam` on disconnected graphs, where `diam` is defined as
`ediam.toNat` and hence maps infinite extended diameter to `0`. -/
def IsHR {n : ℕ} (r : ℕ) (G : SimpleGraph (Fin n)) (m : ℕ) : Prop :=
  ∃ H : SimpleGraph (Fin n),
    G ≤ H ∧
      H.CliqueFree 3 ∧
        H.ediam ≤ (r : ℕ∞) ∧
          addedEdgeCount G H = m ∧
            ∀ K : SimpleGraph (Fin n),
              G ≤ K → K.CliqueFree 3 → K.ediam ≤ (r : ℕ∞) → m ≤ addedEdgeCount G K

/-- The original positive conjecture in Erdős Problem 619. -/
def erdos_619_conjecture : Prop :=
  ∃ c : ℝ,
    0 < c ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (m : ℕ),
        G.Connected →
          G.CliqueFree 3 →
            IsHR 4 G m →
              (m : ℝ) < (1 - c) * n

/-- The target statement for this project: the negation of Erdős Problem 619's conjecture. -/
def erdos_619 : Prop :=
  ¬ erdos_619_conjecture

end

noncomputable section

/-
This file is a proof scaffold for the write-up in `Erdos/solution.md`.

The host-graph existence input is isolated as the import-facing Lemma E theorem below.  The
downstream proof objects are written so that follow-up work can replace that theorem with the
finite-counting development from `LemmaEHostGraphs.lean` while keeping this dependency graph
stable.
-/

/-- Maximum-degree bound, stated pointwise to avoid depending on a particular max-degree API. -/
def MaxDegreeAtMost {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) : Prop :=
  ∀ v : Fin n, (G.neighborSet v).ncard ≤ d

/-- The independence-number constant supplied by the finite-counting Lemma E route. -/
def hostC : ℝ := 15

/-- Lemma E's target host-graph package. -/
def HostGraph (d m : ℕ) (H : SimpleGraph (Fin m)) : Prop :=
  H.Connected ∧
    H.CliqueFree 3 ∧
      MaxDegreeAtMost H d ∧
        (H.indepNum : ℝ) ≤ hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ)

lemma HostGraph.connected {d m : ℕ} {H : SimpleGraph (Fin m)}
    (h : HostGraph d m H) : H.Connected := h.1

lemma HostGraph.cliqueFree_three {d m : ℕ} {H : SimpleGraph (Fin m)}
    (h : HostGraph d m H) : H.CliqueFree 3 := h.2.1

lemma HostGraph.maxDegreeAtMost {d m : ℕ} {H : SimpleGraph (Fin m)}
    (h : HostGraph d m H) : MaxDegreeAtMost H d := h.2.2.1

lemma HostGraph.indepNum_le {d m : ℕ} {H : SimpleGraph (Fin m)}
    (h : HostGraph d m H) :
    (H.indepNum : ℝ) ≤ hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) := h.2.2.2

def AdjacentPairSet {n : ℕ} (H : SimpleGraph (Fin n)) : Set (Fin n × Fin n) :=
  {p | H.Adj p.1 p.2}

def adjacentPairSetEquivSigma {n : ℕ} (H : SimpleGraph (Fin n)) :
    AdjacentPairSet H ≃ Σ v : Fin n, H.neighborSet v where
  toFun p := ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
  invFun q := ⟨(q.1, q.2.1), q.2.2⟩
  left_inv := by
    rintro ⟨⟨v, w⟩, h⟩
    rfl
  right_inv := by
    rintro ⟨v, ⟨w, h⟩⟩
    rfl

lemma adjacentPairSet_nat_card_le_card_mul_of_maxDegreeAtMost {n d : ℕ} {H : SimpleGraph (Fin n)}
    (hdeg : MaxDegreeAtMost H d) : Nat.card (AdjacentPairSet H) ≤ n * d := by
  classical
  have hcard : Nat.card (AdjacentPairSet H) = ∑ v : Fin n, (H.neighborSet v).ncard := by
    calc
      Nat.card (AdjacentPairSet H) = Nat.card (Σ v : Fin n, H.neighborSet v) :=
        Nat.card_congr (adjacentPairSetEquivSigma H)
      _ = ∑ v : Fin n, Nat.card (H.neighborSet v) := by
        rw [Nat.card_sigma]
      _ = ∑ v : Fin n, (H.neighborSet v).ncard := by
        refine Finset.sum_congr rfl ?_
        intro v _
        simpa [SimpleGraph.neighborSet] using Nat.card_coe_set_eq (H.neighborSet v)
  calc
    Nat.card (AdjacentPairSet H) = ∑ v : Fin n, (H.neighborSet v).ncard := hcard
    _ ≤ ∑ _v : Fin n, d := by
      exact Finset.sum_le_sum fun v _ => hdeg v
    _ = n * d := by simp [Fintype.card_fin]

noncomputable def edgeToAdjacentPair {n : ℕ} (H : SimpleGraph (Fin n))
    (e : H.edgeSet) : AdjacentPairSet H :=
  ⟨e.1.out, by
    rw [AdjacentPairSet]
    change H.Adj e.1.out.1 e.1.out.2
    rw [← SimpleGraph.mem_edgeSet]
    simp [Sym2.mk, e.1.out_eq, e.2]⟩

lemma edgeToAdjacentPair_injective {n : ℕ} (H : SimpleGraph (Fin n)) :
    Function.Injective (edgeToAdjacentPair H) := by
  intro e f hef
  apply Subtype.ext
  have hp : e.1.out = f.1.out := congrArg Subtype.val hef
  have hmk : Sym2.mk e.1.out = Sym2.mk f.1.out := congrArg Sym2.mk hp
  simpa [Sym2.mk, e.1.out_eq, f.1.out_eq] using hmk

lemma edgeSet_nat_card_le_card_mul_of_maxDegreeAtMost {n d : ℕ} {H : SimpleGraph (Fin n)}
    (hdeg : MaxDegreeAtMost H d) : Nat.card H.edgeSet ≤ n * d := by
  classical
  exact (Nat.card_le_card_of_injective (edgeToAdjacentPair H)
    (edgeToAdjacentPair_injective H)).trans
      (adjacentPairSet_nat_card_le_card_mul_of_maxDegreeAtMost hdeg)

lemma HostGraph.edgeSet_nat_card_le_card_mul {d m : ℕ} {H : SimpleGraph (Fin m)}
    (h : HostGraph d m H) : Nat.card H.edgeSet ≤ m * d :=
  edgeSet_nat_card_le_card_mul_of_maxDegreeAtMost h.maxDegreeAtMost


/-- Seed-graph package from the `lemmae.md` replacement strategy.

The `+ 3` spelling avoids truncated subtraction and leaves room for the two reconnection edges
used in the deterministic gluing step.  The constant is the modified value from
`lemmaeupdate.md`. -/
def SeedGraph (d n₀ : ℕ) (G : SimpleGraph (Fin n₀)) : Prop :=
  G.CliqueFree 3 ∧
    (∀ v : Fin n₀, (G.neighborSet v).ncard + 3 ≤ d) ∧
      (G.indepNum : ℝ) ≤ 14 * (n₀ : ℝ) * Real.log (d : ℝ) / (d : ℝ)

namespace SeedCounting

/-- Edge slots of the complete graph on `Fin N`. -/
def Slot (N : ℕ) : Type :=
  {p : Fin N × Fin N // p.1 < p.2}

instance (N : ℕ) : Fintype (Slot N) := by
  unfold Slot
  infer_instance

instance (N : ℕ) : DecidableEq (Slot N) := by
  unfold Slot
  infer_instance

/-- Sample space: a label in `Fin q` on every edge slot. -/
abbrev Sample (N q : ℕ) :=
  Slot N → Fin q

/-- The graph associated to a sample; an edge is present when its slot has label zero. -/
def graphOf {N q : ℕ} (hq : 0 < q) (ω : Sample N q) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel fun u v => ∃ h : u < v, ω ⟨(u, v), h⟩ = ⟨0, hq⟩

lemma graphOf_adj {N q : ℕ} (hq : 0 < q) (ω : Sample N q) (u v : Fin N) :
    (graphOf hq ω).Adj u v ↔
      u ≠ v ∧
        ((∃ h : u < v, ω ⟨(u, v), h⟩ = ⟨0, hq⟩) ∨
          ∃ h : v < u, ω ⟨(v, u), h⟩ = ⟨0, hq⟩) := by
  simp [graphOf, SimpleGraph.fromRel_adj]

/-- The slot determined by a distinct unordered pair, stored in increasing order. -/
def slotOf {N : ℕ} (u v : Fin N) (h : u ≠ v) : Slot N :=
  if huv : u < v then ⟨(u, v), huv⟩
  else ⟨(v, u), lt_of_le_of_ne (not_lt.mp huv) h.symm⟩

@[simp] lemma slotOf_of_lt {N : ℕ} {u v : Fin N} (h : u ≠ v) (huv : u < v) :
    slotOf u v h = ⟨(u, v), huv⟩ := by
  simp [slotOf, huv]

@[simp] lemma slotOf_of_gt {N : ℕ} {u v : Fin N} (h : u ≠ v) (hvu : v < u) :
    slotOf u v h = ⟨(v, u), hvu⟩ := by
  have huv : ¬ u < v := not_lt_of_ge hvu.le
  simp [slotOf, huv]

lemma graphOf_adj_iff_slot {N q : ℕ} (hq : 0 < q) (ω : Sample N q)
    {u v : Fin N} (h : u ≠ v) :
    (graphOf hq ω).Adj u v ↔ ω (slotOf u v h) = ⟨0, hq⟩ := by
  by_cases huv : u < v
  · rw [graphOf_adj hq ω u v, slotOf_of_lt h huv]
    constructor
    · rintro ⟨_, ⟨h', hz⟩ | ⟨hvu, _⟩⟩
      · simpa using hz
      · exact False.elim ((not_lt_of_ge huv.le) hvu)
    · intro hz
      exact ⟨h, Or.inl ⟨huv, hz⟩⟩
  · have hvu : v < u := lt_of_le_of_ne (not_lt.mp huv) h.symm
    rw [graphOf_adj hq ω u v, slotOf_of_gt h hvu]
    constructor
    · rintro ⟨_, ⟨huv', _⟩ | ⟨h', hz⟩⟩
      · exact False.elim (huv huv')
      · simpa using hz
    · intro hz
      exact ⟨h, Or.inr ⟨hvu, hz⟩⟩

@[simp] lemma card_sample (N q : ℕ) :
    Fintype.card (Sample N q) = q ^ Fintype.card (Slot N) := by
  classical
  simp [Sample, Fintype.card_fin]

/-- Witness for a vertex having at least `d - 3` zero-labelled incident slots. -/
def HighDegWitness (N d : ℕ) : Type :=
  {x : Fin N × Finset (Fin N) // x.2.card = d - 3 ∧ x.1 ∉ x.2}

instance (N d : ℕ) : Fintype (HighDegWitness N d) := by
  unfold HighDegWitness
  infer_instance

instance (N d : ℕ) : DecidableEq (HighDegWitness N d) := by
  unfold HighDegWitness
  infer_instance

/-- Count high-degree witnesses directly, avoiding a separate high-degree deletion step. -/
noncomputable def highDegWitnessCount {N q : ℕ} (hq : 0 < q) (d : ℕ)
    (ω : Sample N q) : ℕ := by
  classical
  exact (Finset.univ.filter fun W : HighDegWitness N d =>
    ∀ (t : Fin N) (ht : t ∈ W.1.2),
      ω (slotOf W.1.1 t (by
        intro h
        exact W.2.2 (by simpa [h] using ht))) = ⟨0, hq⟩).card

lemma slotOf_fixed_left_injective {N : ℕ} {v : Fin N} {s : Finset (Fin N)}
    (hv : v ∉ s) :
    Function.Injective fun t : {x // x ∈ s} =>
      slotOf v t.1 (by
        intro h
        exact hv (by
          rw [h]
          exact t.2)) := by
  intro a b hslot
  by_cases hva : v < a.1
  · by_cases hvb : v < b.1
    · have hpair : (v, a.1) = (v, b.1) := by
        simpa [slotOf, hva, hvb] using congrArg (fun e : Slot N => e.1) hslot
      exact Subtype.ext (congrArg Prod.snd hpair)
    · have hpair : (v, a.1) = (b.1, v) := by
        simpa [slotOf, hva, hvb] using congrArg (fun e : Slot N => e.1) hslot
      have hv_eq_b : v = b.1 := congrArg Prod.fst hpair
      exact False.elim (hv (by simpa [← hv_eq_b] using b.2))
  · by_cases hvb : v < b.1
    · have hpair : (a.1, v) = (v, b.1) := by
        simpa [slotOf, hva, hvb] using congrArg (fun e : Slot N => e.1) hslot
      have ha_eq_v : a.1 = v := congrArg Prod.fst hpair
      exact False.elim (hv (by simpa [ha_eq_v] using a.2))
    · have hpair : (a.1, v) = (b.1, v) := by
        simpa [slotOf, hva, hvb] using congrArg (fun e : Slot N => e.1) hslot
      exact Subtype.ext (congrArg Prod.fst hpair)

/-- The forced-zero slots associated to a high-degree witness. -/
def highDegWitnessSlots {N d : ℕ} (W : HighDegWitness N d) : Finset (Slot N) :=
  W.1.2.attach.map
    ⟨fun t => slotOf W.1.1 t.1 (by
        intro h
        exact W.2.2 (by
          rw [h]
          exact t.2)),
      slotOf_fixed_left_injective W.2.2⟩

@[simp] lemma card_highDegWitnessSlots {N d : ℕ} (W : HighDegWitness N d) :
    (highDegWitnessSlots W).card = d - 3 := by
  simp [highDegWitnessSlots, W.2.1]

lemma highDegWitnessSlots_forall_zero_iff {N q d : ℕ} (hq : 0 < q)
    (ω : Sample N q) (W : HighDegWitness N d) :
    (∀ e, e ∈ highDegWitnessSlots W → ω e = ⟨0, hq⟩) ↔
      ∀ (t : Fin N) (ht : t ∈ W.1.2),
        ω (slotOf W.1.1 t (by
          intro h
          exact W.2.2 (by simpa [h] using ht))) = ⟨0, hq⟩ := by
  constructor
  · intro h t ht
    exact h _ (Finset.mem_map.mpr ⟨⟨t, ht⟩, by simp, by apply Subtype.ext; rfl⟩)
  · intro h e he
    rcases Finset.mem_map.mp he with ⟨t, _ht, hte⟩
    rw [← hte]
    exact h t.1 t.2

lemma highDegWitnessCount_eq_zero_iff {N q : ℕ} (hq : 0 < q) (d : ℕ)
    (ω : Sample N q) :
    highDegWitnessCount hq d ω = 0 ↔
      ∀ W : HighDegWitness N d,
        ¬ (∀ (t : Fin N) (ht : t ∈ W.1.2),
          ω (slotOf W.1.1 t (by
            intro h
            exact W.2.2 (by simpa [h] using ht))) = ⟨0, hq⟩) := by
  classical
  simp [highDegWitnessCount]

lemma degree_add_three_le_of_highDegWitnessCount_eq_zero {N q d : ℕ} (hq : 0 < q)
    (ω : Sample N q) (hd : 3 ≤ d) (hzero : highDegWitnessCount hq d ω = 0) :
    ∀ v : Fin N, ((graphOf hq ω).neighborSet v).ncard + 3 ≤ d := by
  classical
  intro v
  by_contra hnot
  let S := ((graphOf hq ω).neighborSet v).toFinset
  have hScard : S.card = ((graphOf hq ω).neighborSet v).ncard := by
    calc
      S.card = Fintype.card ((graphOf hq ω).neighborSet v) := by
        simp [S]
      _ = ((graphOf hq ω).neighborSet v).ncard := by
        rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  have hle : d - 3 ≤ S.card := by
    omega
  rcases Finset.exists_subset_card_eq (s := S) (n := d - 3) hle with ⟨T, hTS, hTcard⟩
  have hvnot : v ∉ T := by
    intro hvT
    have hvS : v ∈ S := hTS hvT
    have hvadj : (graphOf hq ω).Adj v v := by
      simp [S] at hvS
    exact (graphOf hq ω).irrefl hvadj
  let W : HighDegWitness N d := ⟨(v, T), hTcard, hvnot⟩
  have hpred :
      ∀ (t : Fin N) (ht : t ∈ W.1.2),
        ω (slotOf W.1.1 t (by
          intro h
          exact W.2.2 (by simpa [h] using ht))) = ⟨0, hq⟩ := by
    intro t ht
    have htT : t ∈ T := ht
    have htS : t ∈ S := hTS htT
    have hadj : (graphOf hq ω).Adj v t := by
      simpa [S] using htS
    have hvne : v ≠ t := (graphOf_adj hq ω v t).1 hadj |>.1
    simpa [W] using (graphOf_adj_iff_slot hq ω hvne).1 hadj
  exact ((highDegWitnessCount_eq_zero_iff hq d ω).1 hzero W) hpred

/-- Witness for an independent set of a prescribed cardinality. -/
def IndepWitness (N k : ℕ) : Type :=
  {A : Finset (Fin N) // A.card = k}

instance (N k : ℕ) : Fintype (IndepWitness N k) := by
  unfold IndepWitness
  infer_instance

instance (N k : ℕ) : DecidableEq (IndepWitness N k) := by
  unfold IndepWitness
  infer_instance

/-- Count `k`-sets whose internal slots are all nonzero. -/
noncomputable def indepWitnessCount {N q : ℕ} (hq : 0 < q) (k : ℕ)
    (ω : Sample N q) : ℕ := by
  classical
  exact (Finset.univ.filter fun A : IndepWitness N k =>
    ∀ (u : Fin N), u ∈ A.1 → ∀ (v : Fin N), v ∈ A.1 → ∀ h : u ≠ v,
      ω (slotOf u v h) ≠ ⟨0, hq⟩).card

lemma card_offDiag_filter_lt_fin {N : ℕ} (s : Finset (Fin N)) :
    (s.offDiag.filter fun p : Fin N × Fin N => p.1 < p.2).card = s.card.choose 2 := by
  classical
  rw [← Sym2.card_image_offDiag s]
  refine Finset.card_bij (s := s.offDiag.filter fun p : Fin N × Fin N => p.1 < p.2)
    (t := s.offDiag.image Sym2.mk)
    (fun p _ => Sym2.mk p) ?hi ?hinj ?hsurj
  · intro p hp
    exact Finset.mem_image.mpr ⟨p, (Finset.mem_filter.mp hp).1, rfl⟩
  · intro p hp q hq hsym
    have hplt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    have hqlt : q.1 < q.2 := (Finset.mem_filter.mp hq).2
    rw [Sym2.eq_iff] at hsym
    rcases hsym with hpq | hpq
    · exact Prod.ext hpq.1 hpq.2
    · have : q.2 < q.1 := by simpa [hpq.1, hpq.2] using hplt
      exact False.elim ((not_lt_of_ge hqlt.le) this)
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
    have hpne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    by_cases hlt : p.1 < p.2
    · exact ⟨p, Finset.mem_filter.mpr ⟨hp, hlt⟩, rfl⟩
    · have hgt : p.2 < p.1 := lt_of_le_of_ne (not_lt.mp hlt) hpne.symm
      refine ⟨(p.2, p.1), Finset.mem_filter.mpr ?_, ?_⟩
      · exact ⟨Finset.mem_offDiag.mpr ⟨(Finset.mem_offDiag.mp hp).2.1,
          (Finset.mem_offDiag.mp hp).1, hpne.symm⟩, hgt⟩
      · rw [Sym2.eq_swap]

/-- The unordered internal slots of an independent-set witness, represented by ordered pairs
`u < v`. -/


lemma card_slot (N : ℕ) :
    Fintype.card (Slot N) = N.choose 2 := by
  classical
  rw [show Fintype.card (Slot N) =
      ((Finset.univ : Finset (Fin N × Fin N)).filter fun p => p.1 < p.2).card by
    simp [Slot, Fintype.card_subtype]]
  rw [show ((Finset.univ : Finset (Fin N × Fin N)).filter fun p => p.1 < p.2) =
      ((Finset.univ : Finset (Fin N)).offDiag.filter fun p : Fin N × Fin N => p.1 < p.2) by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hp
      exact ⟨Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, ne_of_lt hp⟩, hp⟩
    · intro hp
      exact hp.2]
  simpa using card_offDiag_filter_lt_fin (Finset.univ : Finset (Fin N))

def indepWitnessSlots {N k : ℕ} (A : IndepWitness N k) : Finset (Slot N) :=
  (A.1.offDiag.filter fun p : Fin N × Fin N => p.1 < p.2).attach.map
    ⟨fun p => (⟨p.1, by simpa using (Finset.mem_filter.mp p.2).2⟩ : Slot N),
      by
        intro p q hpq
        apply Subtype.ext
        exact congrArg (fun e : Slot N => e.1) hpq⟩

@[simp] lemma card_indepWitnessSlots {N k : ℕ} (A : IndepWitness N k) :
    (indepWitnessSlots A).card =
      (A.1.offDiag.filter fun p : Fin N × Fin N => p.1 < p.2).card := by
  simp [indepWitnessSlots]

lemma card_indepWitnessSlots_choose {N k : ℕ} (A : IndepWitness N k) :
    (indepWitnessSlots A).card = k.choose 2 := by
  rw [card_indepWitnessSlots, card_offDiag_filter_lt_fin]
  simpa using congrArg (fun n : ℕ => n.choose 2) A.2

lemma indepWitnessSlots_forall_nonzero_iff {N q k : ℕ} (hq : 0 < q)
    (ω : Sample N q) (A : IndepWitness N k) :
    (∀ e, e ∈ indepWitnessSlots A → ω e ≠ ⟨0, hq⟩) ↔
      ∀ (u : Fin N), u ∈ A.1 → ∀ (v : Fin N), v ∈ A.1 → ∀ h : u ≠ v,
        ω (slotOf u v h) ≠ ⟨0, hq⟩ := by
  constructor
  · intro h u hu v hv huv
    by_cases huvlt : u < v
    · have hmem : (⟨(u, v), huvlt⟩ : Slot N) ∈ indepWitnessSlots A := by
        refine Finset.mem_map.mpr ⟨⟨(u, v), ?_⟩, by simp, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hu, hv, huv⟩, huvlt⟩
      simpa [slotOf_of_lt huv huvlt] using h _ hmem
    · have hvult : v < u := lt_of_le_of_ne (not_lt.mp huvlt) huv.symm
      have hmem : (⟨(v, u), hvult⟩ : Slot N) ∈ indepWitnessSlots A := by
        refine Finset.mem_map.mpr ⟨⟨(v, u), ?_⟩, by simp, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hv, hu, huv.symm⟩, hvult⟩
      simpa [slotOf_of_gt huv hvult] using h _ hmem
  · intro h e he
    rcases Finset.mem_map.mp he with ⟨p, _hp, hpe⟩
    rcases p with ⟨⟨u, v⟩, hp⟩
    have hp' := Finset.mem_filter.mp hp
    have hu : u ∈ A.1 := (Finset.mem_offDiag.mp hp'.1).1
    have hv : v ∈ A.1 := (Finset.mem_offDiag.mp hp'.1).2.1
    have huvne : u ≠ v := (Finset.mem_offDiag.mp hp'.1).2.2
    have huvlt : u < v := hp'.2
    rw [← hpe]
    simpa [slotOf_of_lt huvne huvlt] using h u hu v hv huvne

lemma indepWitnessCount_eq_zero_iff {N q : ℕ} (hq : 0 < q) (k : ℕ)
    (ω : Sample N q) :
    indepWitnessCount hq k ω = 0 ↔
      ∀ A : IndepWitness N k,
        ¬ (∀ (u : Fin N), u ∈ A.1 → ∀ (v : Fin N), v ∈ A.1 → ∀ h : u ≠ v,
          ω (slotOf u v h) ≠ ⟨0, hq⟩) := by
  classical
  simp [indepWitnessCount]

lemma indepNum_lt_of_indepWitnessCount_eq_zero {N q k : ℕ} (hq : 0 < q)
    (ω : Sample N q) (hzero : indepWitnessCount hq k ω = 0) :
    (graphOf hq ω).indepNum < k := by
  classical
  by_contra hnot
  have hk : k ≤ (graphOf hq ω).indepNum := le_of_not_gt hnot
  rcases (graphOf hq ω).exists_isNIndepSet_indepNum with ⟨s, hs⟩
  rcases Finset.exists_subset_card_eq (s := s) (n := k) (by simpa [hs.card_eq] using hk) with
    ⟨t, hts, htcard⟩
  let A : IndepWitness N k := ⟨t, htcard⟩
  have hpred :
      ∀ (u : Fin N), u ∈ A.1 → ∀ (v : Fin N), v ∈ A.1 → ∀ h : u ≠ v,
        ω (slotOf u v h) ≠ ⟨0, hq⟩ := by
    intro u hu v hv huv hslot
    have hadj : (graphOf hq ω).Adj u v := (graphOf_adj_iff_slot hq ω huv).2 hslot
    exact hs.isIndepSet (hts hu) (hts hv) huv hadj
  exact ((indepWitnessCount_eq_zero_iff hq k ω).1 hzero A) hpred

/-- Ordered triangle witness `u < v < w`. -/
def TriangleWitness (N : ℕ) : Type :=
  {p : Fin N × Fin N × Fin N // p.1 < p.2.1 ∧ p.2.1 < p.2.2}

instance (N : ℕ) : Fintype (TriangleWitness N) := by
  unfold TriangleWitness
  infer_instance

instance (N : ℕ) : DecidableEq (TriangleWitness N) := by
  unfold TriangleWitness
  infer_instance

lemma card_triangleWitness_le_cube (N : ℕ) :
    Fintype.card (TriangleWitness N) ≤ N ^ 3 := by
  calc
    Fintype.card (TriangleWitness N) ≤ Fintype.card (Fin N × Fin N × Fin N) :=
      Fintype.card_subtype_le _
    _ = N ^ 3 := by
      simp [Fintype.card_prod, Fintype.card_fin, pow_succ, mul_assoc]

/-- Count labelled triangles directly as ordered triples `u < v < w`. -/
noncomputable def triangleCount {N q : ℕ} (hq : 0 < q) (ω : Sample N q) : ℕ := by
  classical
  exact (Finset.univ.filter fun T : TriangleWitness N =>
    ω ⟨(T.1.1, T.1.2.1), T.2.1⟩ = ⟨0, hq⟩ ∧
      ω ⟨(T.1.2.1, T.1.2.2), T.2.2⟩ = ⟨0, hq⟩ ∧
        ω ⟨(T.1.1, T.1.2.2), T.2.1.trans T.2.2⟩ = ⟨0, hq⟩).card

lemma triangleCount_eq_zero_iff {N q : ℕ} (hq : 0 < q) (ω : Sample N q) :
    triangleCount hq ω = 0 ↔
      ∀ T : TriangleWitness N,
        ¬ (ω ⟨(T.1.1, T.1.2.1), T.2.1⟩ = ⟨0, hq⟩ ∧
          ω ⟨(T.1.2.1, T.1.2.2), T.2.2⟩ = ⟨0, hq⟩ ∧
            ω ⟨(T.1.1, T.1.2.2), T.2.1.trans T.2.2⟩ = ⟨0, hq⟩) := by
  classical
  simp [triangleCount]

/-- The three slots supporting an ordered triangle witness. -/
def triangleSlots {N : ℕ} (T : TriangleWitness N) : Finset (Slot N) :=
  {⟨(T.1.1, T.1.2.1), T.2.1⟩,
    ⟨(T.1.2.1, T.1.2.2), T.2.2⟩,
    ⟨(T.1.1, T.1.2.2), T.2.1.trans T.2.2⟩}

@[simp] lemma card_triangleSlots {N : ℕ} (T : TriangleWitness N) :
    (triangleSlots T).card = 3 := by
  rcases T with ⟨⟨u, v, w⟩, huv, hvw⟩
  have hnot12_23 :
      (⟨(u, v), huv⟩ : Slot N) ≠ ⟨(v, w), hvw⟩ := by
    intro h
    have huv_eq : u = v := by simpa using congrArg (fun e : Slot N => e.1.1) h
    exact (ne_of_lt huv) huv_eq
  have hnot12_13 :
      (⟨(u, v), huv⟩ : Slot N) ≠ ⟨(u, w), huv.trans hvw⟩ := by
    intro h
    have hvw_eq : v = w := by simpa using congrArg (fun e : Slot N => e.1.2) h
    exact (ne_of_lt hvw) hvw_eq
  have hnot23_13 :
      (⟨(v, w), hvw⟩ : Slot N) ≠ ⟨(u, w), huv.trans hvw⟩ := by
    intro h
    have hvu_eq : v = u := by simpa using congrArg (fun e : Slot N => e.1.1) h
    exact (ne_of_gt huv) hvu_eq
  simp [triangleSlots, hnot12_23, hnot12_13, hnot23_13]

lemma triangleSlots_forall_zero_iff {N q : ℕ} (hq : 0 < q) (ω : Sample N q)
    (T : TriangleWitness N) :
    (∀ e, e ∈ triangleSlots T → ω e = ⟨0, hq⟩) ↔
      ω ⟨(T.1.1, T.1.2.1), T.2.1⟩ = ⟨0, hq⟩ ∧
        ω ⟨(T.1.2.1, T.1.2.2), T.2.2⟩ = ⟨0, hq⟩ ∧
          ω ⟨(T.1.1, T.1.2.2), T.2.1.trans T.2.2⟩ = ⟨0, hq⟩ := by
  simp [triangleSlots]

/-- A graph on any finite vertex type satisfying the modified seed bounds. -/
def SeedGraphOn (d : ℕ) {V : Type*} [Finite V] (G : SimpleGraph V) : Prop :=
  G.CliqueFree 3 ∧
    (∀ v : V, (G.neighborSet v).ncard + 3 ≤ d) ∧
      (G.indepNum : ℝ) ≤ 14 * (Nat.card V : ℝ) * Real.log (d : ℝ) / (d : ℝ)

lemma isIndepSet_image_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) {s : Set V} (hs : G.IsIndepSet s) :
    H.IsIndepSet (φ '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne hadj
  exact hs ha hb (fun h => hne (by simp [h])) (φ.map_rel_iff.1 hadj)

lemma isNIndepSet_map_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) {n : ℕ} {s : Finset V} (hs : G.IsNIndepSet n s) :
    H.IsNIndepSet n (s.map φ.toEquiv.toEmbedding) := by
  refine ⟨?_, ?_⟩
  · simpa [Finset.coe_map] using isIndepSet_image_of_iso φ hs.isIndepSet
  · simpa using (Finset.card_map φ.toEquiv.toEmbedding).trans hs.card_eq

lemma isIndepSet_image_of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ↪g H) {s : Set V} (hs : G.IsIndepSet s) :
    H.IsIndepSet (φ '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne hadj
  exact hs ha hb (fun h => hne (by simp [h])) (φ.map_rel_iff.1 hadj)

lemma isNIndepSet_map_of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ↪g H) {n : ℕ} {s : Finset V} (hs : G.IsNIndepSet n s) :
    H.IsNIndepSet n (s.map φ.toEmbedding) := by
  refine ⟨?_, ?_⟩
  · simpa [Finset.coe_map] using isIndepSet_image_of_embedding φ hs.isIndepSet
  · simpa using (Finset.card_map φ.toEmbedding).trans hs.card_eq

lemma indepNum_le_of_embedding {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ↪g H) :
    G.indepNum ≤ H.indepNum := by
  classical
  rcases G.exists_isNIndepSet_indepNum with ⟨s, hs⟩
  have hle := (isNIndepSet_map_of_embedding φ hs).isIndepSet.card_le_indepNum
  simpa [hs.card_eq] using hle

lemma indepNum_induce_le {V : Type*} [Finite V] (G : SimpleGraph V) (s : Set V) :
    (G.induce s).indepNum ≤ G.indepNum := by
  exact indepNum_le_of_embedding (SimpleGraph.Embedding.induce (G := G) s)

lemma indepNum_eq_of_iso {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) :
    G.indepNum = H.indepNum := by
  classical
  apply le_antisymm
  · rcases G.exists_isNIndepSet_indepNum with ⟨s, hs⟩
    have hle := (isNIndepSet_map_of_iso φ hs).isIndepSet.card_le_indepNum
    simpa [hs.card_eq] using hle
  · rcases H.exists_isNIndepSet_indepNum with ⟨s, hs⟩
    have hle := (isNIndepSet_map_of_iso φ.symm hs).isIndepSet.card_le_indepNum
    simpa [hs.card_eq] using hle

lemma neighborSet_ncard_eq_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (v : V) :
    (H.neighborSet (φ v)).ncard = (G.neighborSet v).ncard := by
  have himage : φ '' G.neighborSet v = H.neighborSet (φ v) := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact φ.map_rel_iff.2 hu
    · intro hw
      refine ⟨φ.symm w, ?_, by simp⟩
      exact φ.map_rel_iff.1 (by simpa using hw)
  rw [← himage]
  simpa using (Set.ncard_image_of_injective (G.neighborSet v) φ.toEquiv.injective)

lemma neighborSet_ncard_induce_le {V : Type*} [Finite V] (G : SimpleGraph V) (s : Set V)
    (v : s) :
    ((G.induce s).neighborSet v).ncard ≤ (G.neighborSet v.1).ncard := by
  exact Set.ncard_le_ncard_of_injOn (fun x : s => (x : V))
    (fun x hx => by simpa using hx)
    (by intro a _ b _ h; exact Subtype.ext h)


/-- Host-graph package on an arbitrary finite vertex type. -/
def HostGraphOn (d : ℕ) {V : Type*} [Finite V] (H : SimpleGraph V) : Prop :=
  H.Connected ∧
    H.CliqueFree 3 ∧
      (∀ v : V, (H.neighborSet v).ncard ≤ d) ∧
        (H.indepNum : ℝ) ≤ 15 * (Nat.card V : ℝ) * Real.log (d : ℝ) / (d : ℝ)

lemma connected_iff_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) : G.Connected ↔ H.Connected := by
  constructor
  · intro hG
    refine { preconnected := ?_, nonempty := ?_ }
    · intro x y
      obtain ⟨x', rfl⟩ := φ.toEquiv.surjective x
      obtain ⟨y', rfl⟩ := φ.toEquiv.surjective y
      exact (hG.preconnected x' y').map φ.toHom
    · exact hG.nonempty.map φ
  · intro hH
    refine { preconnected := ?_, nonempty := ?_ }
    · intro x y
      have h := hH.preconnected (φ x) (φ y)
      simpa using h.map φ.symm.toHom
    · exact hH.nonempty.map φ.symm

lemma hostGraph_of_hostGraphOn {d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    {H : SimpleGraph V} (hH : HostGraphOn d H) :
    ∃ K : SimpleGraph (Fin (Fintype.card V)), HostGraph d (Fintype.card V) K := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let K : SimpleGraph (Fin (Fintype.card V)) := H.map e.toEmbedding
  let φ : H ≃g K := SimpleGraph.Iso.map e H
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · exact (connected_iff_of_iso φ).1 hH.1
  · simpa [K] using (SimpleGraph.cliqueFree_map_iff (G := H) (f := e.toEmbedding)).2 hH.2.1
  · intro v
    obtain ⟨u, rfl⟩ := e.surjective v
    have hn := hH.2.2.1 u
    rw [← neighborSet_ncard_eq_of_iso φ u] at hn
    have hφu : φ u = e u := rfl
    simpa [K, hφu] using hn
  · have hi := hH.2.2.2
    rw [Nat.card_eq_fintype_card] at hi
    rw [← indepNum_eq_of_iso φ]
    simpa [K] using hi

lemma seedGraph_of_seedGraphOn {d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} (hG : SeedGraphOn d G) :
    ∃ H : SimpleGraph (Fin (Fintype.card V)), SeedGraph d (Fintype.card V) H := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let H : SimpleGraph (Fin (Fintype.card V)) := G.map e.toEmbedding
  let φ : G ≃g H := SimpleGraph.Iso.map e G
  refine ⟨H, ?_, ?_, ?_⟩
  · simpa [H] using (SimpleGraph.cliqueFree_map_iff (G := G) (f := e.toEmbedding)).2 hG.1
  · intro v
    obtain ⟨u, rfl⟩ := e.surjective v
    have hn := hG.2.1 u
    rw [← neighborSet_ncard_eq_of_iso φ u] at hn
    have hφu : φ u = e u := rfl
    simpa [H, hφu] using hn
  · have hi := hG.2.2
    rw [Nat.card_eq_fintype_card] at hi
    rw [← indepNum_eq_of_iso φ]
    simpa [H] using hi


/-- Markov's inequality for finite counting with natural-valued functions. -/
lemma card_filter_mul_le_sum_of_le {α : Type*} [Fintype α] (f : α → ℕ) (a : ℕ) :
    (Finset.univ.filter fun x : α => a ≤ f x).card * a ≤ ∑ x, f x := by
  classical
  calc
    (Finset.univ.filter fun x : α => a ≤ f x).card * a
        = ∑ x ∈ Finset.univ.filter (fun x : α => a ≤ f x), a := by
          simp [Finset.sum_const, mul_comm]
    _ ≤ ∑ x ∈ Finset.univ.filter (fun x : α => a ≤ f x), f x := by
          exact Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
    _ ≤ ∑ x, f x := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (by intro x _ _; exact Nat.zero_le _)



/-- Functions with prescribed values on `s` are equivalent to arbitrary functions on the
complement of `s`. -/
def fixedOnEquiv {ι γ : Type*} [DecidableEq ι] (s : Finset ι) (a : γ) :
    {f : ι → γ // ∀ i, i ∈ s → f i = a} ≃ ({i : ι // i ∉ s} → γ) where
  toFun f i := f.1 i.1
  invFun g :=
    ⟨fun i => if h : i ∈ s then a else g ⟨i, h⟩, by
      intro i hi
      simp [hi]
    ⟩
  left_inv f := by
    ext i
    by_cases hi : i ∈ s
    · simp [hi, f.2 i hi]
    · simp [hi]
  right_inv g := by
    ext i
    simp [i.2]

/-- Count functions with a fixed value on a finite set of coordinates. -/
lemma card_filter_forall_eq {ι γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype γ]
    [DecidableEq γ] (s : Finset ι) (a : γ) :
    (Finset.univ.filter fun f : ι → γ => ∀ i, i ∈ s → f i = a).card =
      Fintype.card γ ^ (Fintype.card ι - s.card) := by
  classical
  rw [← Fintype.card_subtype (fun f : ι → γ => ∀ i, i ∈ s → f i = a)]
  rw [Fintype.card_congr (fixedOnEquiv s a)]
  rw [Fintype.card_pi]
  have hcomp : Fintype.card {i : ι // i ∉ s} = Fintype.card ι - s.card := by
    rw [Fintype.card_subtype (fun i : ι => i ∉ s)]
    have hfilter : (Finset.univ.filter fun i : ι => i ∉ s) = sᶜ := by
      ext i
      simp
    rw [hfilter, Finset.card_compl]
  simp [hcomp]

/-- Count samples whose labels are forced to zero on a chosen slot set. -/
lemma card_forced_zero {N q : ℕ} (hq : 0 < q) (Z : Finset (Slot N)) :
    (Finset.univ.filter fun ω : Sample N q =>
        ∀ e, e ∈ Z → ω e = ⟨0, hq⟩).card =
      q ^ (Fintype.card (Slot N) - Z.card) := by
  simpa [Sample, Fintype.card_fin] using
    (card_filter_forall_eq (ι := Slot N) (γ := Fin q) Z ⟨0, hq⟩)


lemma card_highDegWitness_forced_zero {N q d : ℕ} (hq : 0 < q)
    (W : HighDegWitness N d) :
    (Finset.univ.filter fun ω : Sample N q =>
      ∀ (t : Fin N) (ht : t ∈ W.1.2),
        ω (slotOf W.1.1 t (by
          intro h
          exact W.2.2 (by simpa [h] using ht))) = ⟨0, hq⟩).card =
      q ^ (Fintype.card (Slot N) - (d - 3)) := by
  calc
    (Finset.univ.filter fun ω : Sample N q =>
      ∀ (t : Fin N) (ht : t ∈ W.1.2),
        ω (slotOf W.1.1 t (by
          intro h
          exact W.2.2 (by simpa [h] using ht))) = ⟨0, hq⟩).card
        = q ^ (Fintype.card (Slot N) - (highDegWitnessSlots W).card) := by
          convert card_forced_zero hq (highDegWitnessSlots W) using 2
          ext ω
          simpa using (highDegWitnessSlots_forall_zero_iff hq ω W).symm
    _ = q ^ (Fintype.card (Slot N) - (d - 3)) := by
          simp [card_highDegWitnessSlots W]

lemma sum_highDegWitnessCount {N q d : ℕ} (hq : 0 < q) :
    (∑ ω : Sample N q, highDegWitnessCount hq d ω) =
      Fintype.card (HighDegWitness N d) * q ^ (Fintype.card (Slot N) - (d - 3)) := by
  classical
  simp_rw [highDegWitnessCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  simp [card_highDegWitness_forced_zero hq, Finset.sum_const]

lemma card_triangle_forced_zero {N q : ℕ} (hq : 0 < q) (T : TriangleWitness N) :
    (Finset.univ.filter fun ω : Sample N q =>
      ω ⟨(T.1.1, T.1.2.1), T.2.1⟩ = ⟨0, hq⟩ ∧
        ω ⟨(T.1.2.1, T.1.2.2), T.2.2⟩ = ⟨0, hq⟩ ∧
          ω ⟨(T.1.1, T.1.2.2), T.2.1.trans T.2.2⟩ = ⟨0, hq⟩).card =
      q ^ (Fintype.card (Slot N) - 3) := by
  rw [← card_triangleSlots T]
  convert card_forced_zero hq (triangleSlots T) using 2
  ext ω
  simpa using (triangleSlots_forall_zero_iff hq ω T).symm

lemma sum_triangleCount {N q : ℕ} (hq : 0 < q) :
    (∑ ω : Sample N q, triangleCount hq ω) =
      Fintype.card (TriangleWitness N) * q ^ (Fintype.card (Slot N) - 3) := by
  classical
  simp_rw [triangleCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  simp [card_triangle_forced_zero hq, Finset.sum_const]

/-- Functions avoiding a prescribed value on `s` split into nonzero choices on `s` and arbitrary
choices off `s`. -/
def avoidOnEquiv {ι γ : Type*} [DecidableEq ι] [DecidableEq γ] (s : Finset ι) (a : γ) :
    {f : ι → γ // ∀ i, i ∈ s → f i ≠ a} ≃
      (({i : ι // i ∈ s} → {x : γ // x ≠ a}) × ({i : ι // i ∉ s} → γ)) where
  toFun f :=
    (fun i => ⟨f.1 i.1, f.2 i.1 i.2⟩, fun i => f.1 i.1)
  invFun g :=
    ⟨fun i => if h : i ∈ s then (g.1 ⟨i, h⟩).1 else g.2 ⟨i, h⟩, by
      intro i hi
      simp [hi, (g.1 ⟨i, hi⟩).2]
    ⟩
  left_inv f := by
    ext i
    by_cases hi : i ∈ s
    · simp [hi]
    · simp [hi]
  right_inv g := by
    rcases g with ⟨gS, gC⟩
    ext i <;> simp [i.2]

/-- Count functions avoiding a fixed value on a finite set of coordinates. -/
lemma card_filter_forall_ne {ι γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype γ]
    [DecidableEq γ] (s : Finset ι) (a : γ) :
    (Finset.univ.filter fun f : ι → γ => ∀ i, i ∈ s → f i ≠ a).card =
      (Fintype.card γ - 1) ^ s.card * Fintype.card γ ^ (Fintype.card ι - s.card) := by
  classical
  rw [← Fintype.card_subtype (fun f : ι → γ => ∀ i, i ∈ s → f i ≠ a)]
  rw [Fintype.card_congr (avoidOnEquiv s a)]
  rw [Fintype.card_prod]
  rw [Fintype.card_pi, Fintype.card_pi]
  have hS : Fintype.card {i : ι // i ∈ s} = s.card := by
    rw [Fintype.card_subtype (fun i : ι => i ∈ s)]
    have hfilter : (Finset.univ.filter fun i : ι => i ∈ s) = s := by
      ext i
      simp
    rw [hfilter]
  have hC : Fintype.card {i : ι // i ∉ s} = Fintype.card ι - s.card := by
    rw [Fintype.card_subtype (fun i : ι => i ∉ s)]
    have hfilter : (Finset.univ.filter fun i : ι => i ∉ s) = sᶜ := by
      ext i
      simp
    rw [hfilter, Finset.card_compl]
  have hne : Fintype.card {x : γ // x ≠ a} = Fintype.card γ - 1 := by
    simp
  simp [hC, hne]

/-- Count samples where a chosen slot set is forced to avoid zero. -/
lemma card_forced_nonzero {N q : ℕ} (hq : 0 < q) (T : Finset (Slot N)) :
    (Finset.univ.filter fun ω : Sample N q =>
        ∀ e, e ∈ T → ω e ≠ ⟨0, hq⟩).card =
      (q - 1) ^ T.card * q ^ (Fintype.card (Slot N) - T.card) := by
  simpa [Sample, Fintype.card_fin] using
    (card_filter_forall_ne (ι := Slot N) (γ := Fin q) T ⟨0, hq⟩)

/-- Count samples with a prescribed zero/nonzero pattern on a finite slot set. -/
lemma card_indepWitness_forced_nonzero {N q k : ℕ} (hq : 0 < q)
    (A : IndepWitness N k) :
    (Finset.univ.filter fun ω : Sample N q =>
      ∀ (u : Fin N), u ∈ A.1 → ∀ (v : Fin N), v ∈ A.1 → ∀ h : u ≠ v,
        ω (slotOf u v h) ≠ ⟨0, hq⟩).card =
      (q - 1) ^ (indepWitnessSlots A).card *
        q ^ (Fintype.card (Slot N) - (indepWitnessSlots A).card) := by
  convert card_forced_nonzero hq (indepWitnessSlots A) using 2
  ext ω
  simpa using (indepWitnessSlots_forall_nonzero_iff hq ω A).symm

lemma sum_indepWitnessCount {N q k : ℕ} (hq : 0 < q) :
    (∑ ω : Sample N q, indepWitnessCount hq k ω) =
      ∑ A : IndepWitness N k,
        (q - 1) ^ (indepWitnessSlots A).card *
          q ^ (Fintype.card (Slot N) - (indepWitnessSlots A).card) := by
  classical
  simp_rw [indepWitnessCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  simp [card_indepWitness_forced_nonzero hq]

lemma sum_indepWitnessCount_eq {N q k : ℕ} (hq : 0 < q) :
    (∑ ω : Sample N q, indepWitnessCount hq k ω) =
      Fintype.card (IndepWitness N k) *
        ((q - 1) ^ (k.choose 2) * q ^ (Fintype.card (Slot N) - k.choose 2)) := by
  rw [sum_indepWitnessCount]
  simp only [card_indepWitnessSlots_choose]
  simp [Finset.sum_const, Finset.card_univ]

lemma card_pattern {N q : ℕ} (hq : 0 < q) (T Z : Finset (Slot N)) (hZ : Z ⊆ T) :
    (Finset.univ.filter fun ω : Sample N q =>
        (∀ e, e ∈ Z → ω e = ⟨0, hq⟩) ∧
          ∀ e, e ∈ T \ Z → ω e ≠ ⟨0, hq⟩).card =
      (q - 1) ^ (T.card - Z.card) * q ^ (Fintype.card (Slot N) - T.card) := by
  classical
  let A : Finset (Slot N) := Z
  let B : Finset (Slot N) := T \ Z
  have hAunionB : A ∪ B = T := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_union.mp he with heA | heB
      · exact hZ (by simpa [A] using heA)
      · exact (Finset.mem_sdiff.mp (by simpa [B] using heB)).1
    · intro heT
      by_cases heZ : e ∈ Z
      · exact Finset.mem_union_left _ (by simpa [A] using heZ)
      · exact Finset.mem_union_right _ (by simpa [B] using ⟨heT, heZ⟩)
  rw [← Fintype.card_subtype (fun ω : Sample N q =>
      (∀ e, e ∈ Z → ω e = ⟨0, hq⟩) ∧
        ∀ e, e ∈ T \ Z → ω e ≠ ⟨0, hq⟩)]
  let patternEquiv :
      {ω : Sample N q //
        (∀ e, e ∈ Z → ω e = ⟨0, hq⟩) ∧
          ∀ e, e ∈ T \ Z → ω e ≠ ⟨0, hq⟩} ≃
        (({e : Slot N // e ∈ B} → {x : Fin q // x ≠ ⟨0, hq⟩}) ×
          ({e : Slot N // e ∉ A ∪ B} → Fin q)) :=
    { toFun := fun ω =>
        (fun e => ⟨ω.1 e.1, ω.2.2 e.1 (by
          change e.1 ∈ B
          exact e.2)⟩,
          fun e => ω.1 e.1)
      invFun := fun g =>
        ⟨fun e =>
            if hA : e ∈ A then ⟨0, hq⟩
            else if hB : e ∈ B then (g.1 ⟨e, hB⟩).1
            else g.2 ⟨e, by simp [hA, hB]⟩,
          by
            constructor
            · intro e he
              have hA : e ∈ A := by simpa [A] using he
              simp [hA]
            · intro e he
              have hnotA : e ∉ A := by
                intro hA
                exact (Finset.mem_sdiff.mp (by simpa [B] using he)).2 (by simpa [A] using hA)
              have hB : e ∈ B := by simpa [B] using he
              simp [hnotA, hB, (g.1 ⟨e, hB⟩).2]
        ⟩
      left_inv := by
        intro ω
        ext e
        by_cases hA : e ∈ A
        · have hz : e ∈ Z := by simpa [A] using hA
          simp [hA, ω.2.1 e hz]
        · by_cases hB : e ∈ B
          · simp [hA, hB]
          · simp [hA, hB]
      right_inv := by
        intro g
        rcases g with ⟨gB, gC⟩
        apply Prod.ext
        · funext e
          have heB : e.1 ∈ T \ Z := by
            simpa only [B] using e.2
          have hnotA : e.1 ∉ A := by
            intro hA
            exact (Finset.mem_sdiff.mp heB).2 (by simpa [A] using hA)
          simp [hnotA, e.2]
        · funext e
          have hnotA : e.1 ∉ A := (Finset.notMem_union.mp e.2).1
          have hnotB : e.1 ∉ B := (Finset.notMem_union.mp e.2).2
          simp [hnotA, hnotB] }
  rw [Fintype.card_congr patternEquiv]
  rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_pi]
  have hBcardFinset : B.card = T.card - Z.card := by
    simpa [B] using (Finset.card_sdiff_of_subset hZ)
  have hBcard : Fintype.card {e : Slot N // e ∈ B} = T.card - Z.card := by
    rw [Fintype.card_subtype (fun e : Slot N => e ∈ B)]
    have hfilter : (Finset.univ.filter fun e : Slot N => e ∈ B) = B := by
      ext e
      simp
    rw [hfilter, hBcardFinset]
  have hCcard : Fintype.card {e : Slot N // e ∉ A ∧ e ∉ B} =
      Fintype.card (Slot N) - T.card := by
    rw [Fintype.card_subtype (fun e : Slot N => e ∉ A ∧ e ∉ B)]
    have hfilter : (Finset.univ.filter fun e : Slot N => e ∉ A ∧ e ∉ B) = (A ∪ B)ᶜ := by
      ext e
      simp
    rw [hfilter, Finset.card_compl, hAunionB]
  have hne : Fintype.card {x : Fin q // x ≠ ⟨0, hq⟩} = q - 1 := by
    simp [Fintype.card_fin]
  simp [hBcardFinset, hCcard, hne, Fintype.card_fin]

/-- If three bad-event sets have total cardinality below the full sample space, some point avoids
all three. -/
lemma exists_not_of_three_bad_card_sum_lt {α : Type*} [Fintype α]
    (P Q R : α → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (hbad : (Finset.univ.filter P).card + (Finset.univ.filter Q).card +
        (Finset.univ.filter R).card < Fintype.card α) :
    ∃ x : α, ¬ P x ∧ ¬ Q x ∧ ¬ R x := by
  classical
  let bad := Finset.univ.filter fun x : α => P x ∨ Q x ∨ R x
  have hbad_card : bad.card < Fintype.card α := by
    have hQR : (Finset.univ.filter fun x : α => Q x ∨ R x).card ≤
        (Finset.univ.filter Q).card + (Finset.univ.filter R).card := by
      rw [Finset.filter_or]
      exact Finset.card_union_le _ _
    have hPQR : bad.card ≤ (Finset.univ.filter P).card +
        (Finset.univ.filter fun x : α => Q x ∨ R x).card := by
      dsimp [bad]
      rw [Finset.filter_or]
      exact Finset.card_union_le _ _
    omega
  have hlt_univ : bad.card < (Finset.univ : Finset α).card := by
    simpa [Finset.card_univ] using hbad_card
  rcases Finset.exists_mem_notMem_of_card_lt_card hlt_univ with ⟨x, _, hx⟩
  refine ⟨x, ?_, ?_, ?_⟩ <;> intro h
  · exact hx (by simp [bad, h])
  · exact hx (by simp [bad, h])
  · exact hx (by simp [bad, h])

/-- A finite Markov corollary: if the sum of an `ℕ`-valued count is at most `b * a`, then
the number of samples with count at least `a` is at most `b`. -/
lemma card_filter_le_of_sum_le_mul {α : Type*} [Fintype α] (f : α → ℕ)
    {a b : ℕ} (ha : 0 < a) (hsum : (∑ x, f x) ≤ b * a) :
    (Finset.univ.filter fun x : α => a ≤ f x).card ≤ b := by
  have hmark := card_filter_mul_le_sum_of_le f a
  exact le_of_mul_le_mul_right (hmark.trans hsum) ha

/-- Three finite Markov bounds imply the existence of a sample below all three thresholds. -/
lemma exists_lt_of_three_sum_bounds {α : Type*} [Fintype α] (f₁ f₂ f₃ : α → ℕ)
    {a₁ a₂ a₃ b₁ b₂ b₃ : ℕ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (hsum₁ : (∑ x, f₁ x) ≤ b₁ * a₁)
    (hsum₂ : (∑ x, f₂ x) ≤ b₂ * a₂)
    (hsum₃ : (∑ x, f₃ x) ≤ b₃ * a₃)
    (hbad : b₁ + b₂ + b₃ < Fintype.card α) :
    ∃ x : α, f₁ x < a₁ ∧ f₂ x < a₂ ∧ f₃ x < a₃ := by
  classical
  have h₁ := card_filter_le_of_sum_le_mul f₁ ha₁ hsum₁
  have h₂ := card_filter_le_of_sum_le_mul f₂ ha₂ hsum₂
  have h₃ := card_filter_le_of_sum_le_mul f₃ ha₃ hsum₃
  rcases exists_not_of_three_bad_card_sum_lt
      (fun x => a₁ ≤ f₁ x) (fun x => a₂ ≤ f₂ x) (fun x => a₃ ≤ f₃ x)
      (by omega) with ⟨x, hx₁, hx₂, hx₃⟩
  exact ⟨x, Nat.lt_of_not_ge hx₁, Nat.lt_of_not_ge hx₂, Nat.lt_of_not_ge hx₃⟩

/-- Scaled first-moment interface recommended by `update2.md`: if each bad count has
`3 * sum < threshold * |Ω|`, then one sample is below all three thresholds. -/
lemma exists_lt_of_three_scaled_sum_bounds {α : Type*} [Fintype α] (f₁ f₂ f₃ : α → ℕ)
    {a₁ a₂ a₃ : ℕ}
    (hsum₁ : 3 * (∑ x, f₁ x) < a₁ * Fintype.card α)
    (hsum₂ : 3 * (∑ x, f₂ x) < a₂ * Fintype.card α)
    (hsum₃ : 3 * (∑ x, f₃ x) < a₃ * Fintype.card α) :
    ∃ x : α, f₁ x < a₁ ∧ f₂ x < a₂ ∧ f₃ x < a₃ := by
  classical
  let B₁ := (Finset.univ.filter fun x : α => a₁ ≤ f₁ x).card
  let B₂ := (Finset.univ.filter fun x : α => a₂ ≤ f₂ x).card
  let B₃ := (Finset.univ.filter fun x : α => a₃ ≤ f₃ x).card
  have hB₁ : 3 * B₁ < Fintype.card α := by
    have hmark := card_filter_mul_le_sum_of_le f₁ a₁
    change B₁ * a₁ ≤ ∑ x, f₁ x at hmark
    apply Nat.lt_of_mul_lt_mul_right (a := a₁)
    nlinarith [hmark, hsum₁]
  have hB₂ : 3 * B₂ < Fintype.card α := by
    have hmark := card_filter_mul_le_sum_of_le f₂ a₂
    change B₂ * a₂ ≤ ∑ x, f₂ x at hmark
    apply Nat.lt_of_mul_lt_mul_right (a := a₂)
    nlinarith [hmark, hsum₂]
  have hB₃ : 3 * B₃ < Fintype.card α := by
    have hmark := card_filter_mul_le_sum_of_le f₃ a₃
    change B₃ * a₃ ≤ ∑ x, f₃ x at hmark
    apply Nat.lt_of_mul_lt_mul_right (a := a₃)
    nlinarith [hmark, hsum₃]
  have hbad : B₁ + B₂ + B₃ < Fintype.card α := by
    omega
  rcases exists_not_of_three_bad_card_sum_lt
      (fun x => a₁ ≤ f₁ x) (fun x => a₂ ≤ f₂ x) (fun x => a₃ ≤ f₃ x)
      (by simpa [B₁, B₂, B₃] using hbad) with ⟨x, hx₁, hx₂, hx₃⟩
  exact ⟨x, Nat.lt_of_not_ge hx₁, Nat.lt_of_not_ge hx₂, Nat.lt_of_not_ge hx₃⟩



lemma card_indepWitness (N k : ℕ) :
    Fintype.card (IndepWitness N k) = N.choose k := by
  simp [IndepWitness]

lemma card_highDegWitness_le (N d : ℕ) :
    Fintype.card (HighDegWitness N d) ≤ N * N.choose (d - 3) := by
  classical
  let f : HighDegWitness N d → Fin N × {s : Finset (Fin N) // s.card = d - 3} :=
    fun W => (W.1.1, ⟨W.1.2, W.2.1⟩)
  have hf : Function.Injective f := by
    intro W W' h
    rcases W with ⟨⟨v, s⟩, hsW⟩
    rcases W' with ⟨⟨v', s'⟩, hsW'⟩
    simp [f] at h
    rcases h with ⟨hv, hs⟩
    subst v'
    subst s'
    rfl
  have hcard := Fintype.card_le_of_injective f hf
  simpa [f, Fintype.card_prod, Fintype.card_fin, Fintype.card_finset_len] using hcard

lemma exists_sample_of_scaled_sum_bounds {N q d k : ℕ} (hq : 0 < q)
    (hdeg : 3 * (∑ ω : Sample N q, highDegWitnessCount hq d ω) <
      1 * Fintype.card (Sample N q))
    (hindep : 3 * (∑ ω : Sample N q, indepWitnessCount hq k ω) <
      1 * Fintype.card (Sample N q))
    (htri : 3 * (∑ ω : Sample N q, triangleCount hq ω) <
      d ^ 3 * Fintype.card (Sample N q)) :
    ∃ ω : Sample N q,
      highDegWitnessCount hq d ω = 0 ∧ indepWitnessCount hq k ω = 0 ∧
        triangleCount hq ω < d ^ 3 := by
  rcases exists_lt_of_three_scaled_sum_bounds
      (fun ω : Sample N q => highDegWitnessCount hq d ω)
      (fun ω : Sample N q => indepWitnessCount hq k ω)
      (fun ω : Sample N q => triangleCount hq ω) hdeg hindep htri with
    ⟨ω, hω₁, hω₂, hω₃⟩
  exact ⟨ω, Nat.lt_one_iff.mp hω₁, Nat.lt_one_iff.mp hω₂, hω₃⟩

lemma exists_sample_of_explicit_moment_bounds {N q d k : ℕ} (hq : 0 < q)
    (hdeg : 3 * (Fintype.card (HighDegWitness N d) *
        q ^ (Fintype.card (Slot N) - (d - 3))) < Fintype.card (Sample N q))
    (hindep : 3 * (Fintype.card (IndepWitness N k) *
        ((q - 1) ^ (k.choose 2) * q ^ (Fintype.card (Slot N) - k.choose 2))) <
      Fintype.card (Sample N q))
    (htri : 3 * (Fintype.card (TriangleWitness N) *
        q ^ (Fintype.card (Slot N) - 3)) < d ^ 3 * Fintype.card (Sample N q)) :
    ∃ ω : Sample N q,
      highDegWitnessCount hq d ω = 0 ∧ indepWitnessCount hq k ω = 0 ∧
        triangleCount hq ω < d ^ 3 := by
  apply exists_sample_of_scaled_sum_bounds hq
  · simpa [sum_highDegWitnessCount hq, one_mul] using hdeg
  · simpa [sum_indepWitnessCount_eq hq, one_mul] using hindep
  · simpa [sum_triangleCount hq] using htri

lemma exists_sample_of_highDeg_indep_triangle_moments {N q d k : ℕ} (hq : 0 < q)
    (hdeg : 3 * (Fintype.card (HighDegWitness N d) *
        q ^ (Fintype.card (Slot N) - (d - 3))) < Fintype.card (Sample N q))
    (hindep : 3 * (∑ ω : Sample N q, indepWitnessCount hq k ω) <
      Fintype.card (Sample N q))
    (htri : 3 * (Fintype.card (TriangleWitness N) *
        q ^ (Fintype.card (Slot N) - 3)) < d ^ 3 * Fintype.card (Sample N q)) :
    ∃ ω : Sample N q,
      highDegWitnessCount hq d ω = 0 ∧ indepWitnessCount hq k ω = 0 ∧
        triangleCount hq ω < d ^ 3 := by
  apply exists_sample_of_scaled_sum_bounds hq
  · simpa [sum_highDegWitnessCount hq, one_mul] using hdeg
  · simpa [one_mul] using hindep
  · simpa [sum_triangleCount hq] using htri





@[simp] lemma card_sample_choose (N q : ℕ) :
    Fintype.card (Sample N q) = q ^ N.choose 2 := by
  simp [card_slot]

lemma triangle_moment_bound_params {d : ℕ} (hd : 2 ≤ d) :
    3 * (((d ^ 6) ^ 3) *
        (6 * d ^ 5) ^ (Fintype.card (Slot (d ^ 6)) - 3)) <
      d ^ 3 * Fintype.card (Sample (d ^ 6) (6 * d ^ 5)) := by
  have hN : 3 ≤ d ^ 6 := by
    have hpow := Nat.pow_le_pow_left hd 6
    norm_num at hpow
    omega
  have hM : 3 ≤ (d ^ 6).choose 2 := by
    have hchoose := Nat.choose_le_choose 2 hN
    norm_num at hchoose
    exact hchoose
  have hApos : 0 < (6 * d ^ 5) ^ ((d ^ 6).choose 2 - 3) := by positivity
  have hsplit :
      (6 * d ^ 5) ^ (d ^ 6).choose 2 =
        (6 * d ^ 5) ^ ((d ^ 6).choose 2 - 3) * (6 * d ^ 5) ^ 3 := by
    rw [← pow_add, Nat.sub_add_cancel hM]
  have hcoeff : 3 * (d ^ 6) ^ 3 < d ^ 3 * (6 * d ^ 5) ^ 3 := by
    have hdpos : 0 < d := by omega
    have hd18 : 0 < d ^ 18 := by positivity
    nlinarith
  have hmul := Nat.mul_lt_mul_of_pos_right hcoeff hApos
  simp [card_slot]
  rw [hsplit]
  nlinarith

lemma exists_sample_of_cardinal_moment_bounds {N q d k : ℕ} (hq : 0 < q)
    (hdeg : 3 * ((N * N.choose (d - 3)) *
        q ^ (Fintype.card (Slot N) - (d - 3))) < Fintype.card (Sample N q))
    (hindep : 3 * (N.choose k *
        ((q - 1) ^ (k.choose 2) * q ^ (Fintype.card (Slot N) - k.choose 2))) <
      Fintype.card (Sample N q))
    (htri : 3 * (N ^ 3 * q ^ (Fintype.card (Slot N) - 3)) <
      d ^ 3 * Fintype.card (Sample N q)) :
    ∃ ω : Sample N q,
      highDegWitnessCount hq d ω = 0 ∧ indepWitnessCount hq k ω = 0 ∧
        triangleCount hq ω < d ^ 3 := by
  apply exists_sample_of_explicit_moment_bounds hq
  · exact lt_of_le_of_lt
      (Nat.mul_le_mul_left 3
        (Nat.mul_le_mul_right (q ^ (Fintype.card (Slot N) - (d - 3)))
          (card_highDegWitness_le N d))) hdeg
  · simpa [card_indepWitness] using hindep
  · exact lt_of_le_of_lt
      (Nat.mul_le_mul_left 3
        (Nat.mul_le_mul_right (q ^ (Fintype.card (Slot N) - 3))
          (card_triangleWitness_le_cube N))) htri



lemma exists_sample_of_param_moment_bounds {d k : ℕ} (hd : 2 ≤ d)
    (hdeg : 3 * (((d ^ 6) * (d ^ 6).choose (d - 3)) *
        (6 * d ^ 5) ^ ((d ^ 6).choose 2 - (d - 3))) <
      (6 * d ^ 5) ^ (d ^ 6).choose 2)
    (hindep : 3 * ((d ^ 6).choose k *
        (((6 * d ^ 5) - 1) ^ (k.choose 2) *
          (6 * d ^ 5) ^ ((d ^ 6).choose 2 - k.choose 2))) <
      (6 * d ^ 5) ^ (d ^ 6).choose 2) :
    ∃ ω : Sample (d ^ 6) (6 * d ^ 5),
      highDegWitnessCount (by positivity) d ω = 0 ∧
        indepWitnessCount (by positivity) k ω = 0 ∧ triangleCount (by positivity) ω < d ^ 3 := by
  apply exists_sample_of_cardinal_moment_bounds (by positivity)
  · simpa [card_sample_choose, card_slot] using hdeg
  · simpa [card_sample_choose, card_slot] using hindep
  · simpa [card_sample_choose, card_slot] using triangle_moment_bound_params hd



noncomputable def realizedTriangles {N q : ℕ} (hq : 0 < q) (ω : Sample N q) :
    Finset (TriangleWitness N) :=
  Finset.univ.filter fun T : TriangleWitness N =>
    ∀ e, e ∈ triangleSlots T → ω e = ⟨0, hq⟩

@[simp] lemma card_realizedTriangles {N q : ℕ} (hq : 0 < q) (ω : Sample N q) :
    (realizedTriangles hq ω).card = triangleCount hq ω := by
  simp [realizedTriangles, triangleCount, triangleSlots]

def triangleVertexFinset {N : ℕ} (T : TriangleWitness N) : Finset (Fin N) :=
  {T.1.1, T.1.2.1, T.1.2.2}

lemma card_triangleVertexFinset_le {N : ℕ} (T : TriangleWitness N) :
    (triangleVertexFinset T).card ≤ 3 := by
  rcases T with ⟨⟨u, v, w⟩, huv, hvw⟩
  have huvne : u ≠ v := ne_of_lt huv
  have hvwne : v ≠ w := ne_of_lt hvw
  have huwne : u ≠ w := ne_of_lt (huv.trans hvw)
  simp [triangleVertexFinset, huvne, hvwne, huwne]

noncomputable def triangleVertices {N q : ℕ} (hq : 0 < q) (ω : Sample N q) :
    Finset (Fin N) :=
  (realizedTriangles hq ω).biUnion triangleVertexFinset

lemma card_triangleVertices_le {N q : ℕ} (hq : 0 < q) (ω : Sample N q) :
    (triangleVertices hq ω).card ≤ 3 * triangleCount hq ω := by
  calc
    (triangleVertices hq ω).card ≤
        ∑ T ∈ realizedTriangles hq ω, (triangleVertexFinset T).card := by
      simpa [triangleVertices] using
        (Finset.card_biUnion_le (s := realizedTriangles hq ω) (t := triangleVertexFinset))
    _ ≤ ∑ T ∈ realizedTriangles hq ω, 3 := by
      exact Finset.sum_le_sum fun T _ => card_triangleVertexFinset_le T
    _ = 3 * triangleCount hq ω := by
      simp [Nat.mul_comm]



lemma mem_triangleVertices_of_ordered_triangle {N q : ℕ} (hq : 0 < q) (ω : Sample N q)
    {u v w : Fin N} (huv : u < v) (hvw : v < w)
    (huvAdj : (graphOf hq ω).Adj u v) (hvwAdj : (graphOf hq ω).Adj v w)
    (huwAdj : (graphOf hq ω).Adj u w) :
    u ∈ triangleVertices hq ω ∧ v ∈ triangleVertices hq ω ∧ w ∈ triangleVertices hq ω := by
  let T : TriangleWitness N := ⟨(u, v, w), huv, hvw⟩
  have hT : T ∈ realizedTriangles hq ω := by
    simp [realizedTriangles, triangleSlots, T]
    constructor
    · have hne : u ≠ v := ne_of_lt huv
      simpa [slotOf_of_lt hne huv] using (graphOf_adj_iff_slot hq ω hne).1 huvAdj
    constructor
    · have hne : v ≠ w := ne_of_lt hvw
      simpa [slotOf_of_lt hne hvw] using (graphOf_adj_iff_slot hq ω hne).1 hvwAdj
    · have huw : u < w := huv.trans hvw
      have hne : u ≠ w := ne_of_lt huw
      simpa [slotOf_of_lt hne huw] using (graphOf_adj_iff_slot hq ω hne).1 huwAdj
  have hu : u ∈ triangleVertexFinset T := by simp [triangleVertexFinset, T]
  have hv : v ∈ triangleVertexFinset T := by simp [triangleVertexFinset, T]
  have hw : w ∈ triangleVertexFinset T := by simp [triangleVertexFinset, T]
  exact ⟨Finset.mem_biUnion.mpr ⟨T, hT, hu⟩,
    Finset.mem_biUnion.mpr ⟨T, hT, hv⟩,
    Finset.mem_biUnion.mpr ⟨T, hT, hw⟩⟩

lemma mem_triangleVertices_of_triangle {N q : ℕ} (hq : 0 < q) (ω : Sample N q)
    {u v w : Fin N} (huvAdj : (graphOf hq ω).Adj u v)
    (huwAdj : (graphOf hq ω).Adj u w) (hvwAdj : (graphOf hq ω).Adj v w) :
    u ∈ triangleVertices hq ω ∧ v ∈ triangleVertices hq ω ∧ w ∈ triangleVertices hq ω := by
  rcases lt_trichotomy u v with huv | huv_eq | hvu
  · rcases lt_trichotomy v w with hvw | hvw_eq | hwv
    · exact mem_triangleVertices_of_ordered_triangle hq ω huv hvw huvAdj hvwAdj huwAdj
    · exact False.elim (hvwAdj.ne hvw_eq)
    · rcases lt_trichotomy u w with huw | huw_eq | hwu
      · rcases mem_triangleVertices_of_ordered_triangle hq ω huw hwv huwAdj hvwAdj.symm huvAdj with
          ⟨hu, hw, hv⟩
        exact ⟨hu, hv, hw⟩
      · exact False.elim (huwAdj.ne huw_eq)
      · rcases
          mem_triangleVertices_of_ordered_triangle hq ω hwu huv huwAdj.symm huvAdj
            hvwAdj.symm with
          ⟨hw, hu, hv⟩
        exact ⟨hu, hv, hw⟩
  · exact False.elim (huvAdj.ne huv_eq)
  · rcases lt_trichotomy u w with huw | huw_eq | hwu
    · rcases mem_triangleVertices_of_ordered_triangle hq ω hvu huw huvAdj.symm huwAdj hvwAdj with
        ⟨hv, hu, hw⟩
      exact ⟨hu, hv, hw⟩
    · exact False.elim (huwAdj.ne huw_eq)
    · rcases lt_trichotomy v w with hvw | hvw_eq | hwv
      · rcases
          mem_triangleVertices_of_ordered_triangle hq ω hvw hwu hvwAdj huwAdj.symm
            huvAdj.symm with
          ⟨hv, hw, hu⟩
        exact ⟨hu, hv, hw⟩
      · exact False.elim (hvwAdj.ne hvw_eq)
      · rcases
          mem_triangleVertices_of_ordered_triangle hq ω hwv hvu hvwAdj.symm huvAdj.symm
            huwAdj.symm with
          ⟨hw, hv, hu⟩
        exact ⟨hu, hv, hw⟩

lemma cliqueFree_induce_compl_triangleVertices {N q : ℕ} (hq : 0 < q) (ω : Sample N q) :
    ((graphOf hq ω).induce {v : Fin N | v ∉ triangleVertices hq ω}).CliqueFree 3 := by
  classical
  intro s hs
  rw [SimpleGraph.is3Clique_iff] at hs
  rcases hs with ⟨a, b, c, hab, hac, hbc, _⟩
  have habG : (graphOf hq ω).Adj a.1 b.1 := by simpa using hab
  have hacG : (graphOf hq ω).Adj a.1 c.1 := by simpa using hac
  have hbcG : (graphOf hq ω).Adj b.1 c.1 := by simpa using hbc
  have hmem := mem_triangleVertices_of_triangle hq ω habG hacG hbcG
  exact a.2 hmem.1



lemma card_compl_finset_subtype (N : ℕ) (D : Finset (Fin N)) :
    Fintype.card {v : Fin N // v ∉ D} = N - D.card := by
  classical
  rw [Fintype.card_subtype]
  rw [show ({x : Fin N | x ∉ D} : Finset (Fin N)) = Dᶜ by
    ext x
    simp]
  simpa [Fintype.card_fin] using (Finset.card_compl D)

lemma card_survivors_triangleVertices {N q : ℕ} (hq : 0 < q) (ω : Sample N q) :
    Fintype.card {v : Fin N // v ∉ triangleVertices hq ω} =
      N - (triangleVertices hq ω).card := by
  exact card_compl_finset_subtype N (triangleVertices hq ω)



lemma natCard_survivors_triangleVertices {N q : ℕ} (hq : 0 < q) (ω : Sample N q) :
    Nat.card {v : Fin N // v ∉ triangleVertices hq ω} =
      N - (triangleVertices hq ω).card := by
  rw [Nat.card_eq_fintype_card]
  exact card_survivors_triangleVertices hq ω

lemma nonempty_survivors_of_triangle_bound {d q : ℕ} (hq : 0 < q) (ω : Sample (d ^ 6) q)
    (hd : 2 ≤ d) (htri : triangleCount hq ω < d ^ 3) :
    Nonempty {v : Fin (d ^ 6) // v ∉ triangleVertices hq ω} := by
  have hdel_lt : (triangleVertices hq ω).card < d ^ 6 := by
    have hdel_le := card_triangleVertices_le hq ω
    have htri3 : 3 * triangleCount hq ω < 3 * d ^ 3 := by
      exact Nat.mul_lt_mul_of_pos_left htri (by norm_num)
    have hd3_gt3 : 3 < d ^ 3 := by
      have hpow := Nat.pow_le_pow_left hd 3
      norm_num at hpow
      omega
    have hd3_pos : 0 < d ^ 3 := by positivity
    have hpoly : 3 * d ^ 3 < d ^ 6 := by
      calc
        3 * d ^ 3 < d ^ 3 * d ^ 3 := Nat.mul_lt_mul_of_pos_right hd3_gt3 hd3_pos
        _ = d ^ 6 := by ring
    exact lt_of_le_of_lt hdel_le (lt_trans htri3 hpoly)
  rw [← Fintype.card_pos_iff]
  rw [card_survivors_triangleVertices hq ω]
  omega




noncomputable def seedIndepThreshold (d : ℕ) : ℕ :=
  Nat.ceil (13 * (d : ℝ) ^ 5 * Real.log (d : ℝ))


lemma seedIndepThreshold_ge (d : ℕ) :
    13 * (d : ℝ) ^ 5 * Real.log (d : ℝ) ≤ (seedIndepThreshold d : ℝ) := by
  unfold seedIndepThreshold
  exact Nat.le_ceil _

lemma seedIndepThreshold_pos_eventually :
    ∀ᶠ d : ℕ in Filter.atTop, 0 < seedIndepThreshold d := by
  filter_upwards [Filter.eventually_ge_atTop (3 : ℕ)] with d hd
  have hkreal : 0 < (seedIndepThreshold d : ℝ) := by
    have hlog : 0 < Real.log (d : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (by omega : 1 < d))
    exact lt_of_lt_of_le (by positivity) (seedIndepThreshold_ge d)
  exact_mod_cast hkreal

lemma seedIndepThreshold_lt_add_one {d : ℕ} (hd : 1 ≤ d) :
    (seedIndepThreshold d : ℝ) <
      13 * (d : ℝ) ^ 5 * Real.log (d : ℝ) + 1 := by
  unfold seedIndepThreshold
  exact Nat.ceil_lt_add_one (by positivity)

lemma alpha_real_budget_aux {d : ℕ} (hd : 100 ≤ d) :
    13 * (d : ℝ) ^ 5 * Real.log (d : ℝ) + 1 ≤
      14 * (((d : ℝ) ^ 6 - 3 * (d : ℝ) ^ 3)) * Real.log (d : ℝ) / (d : ℝ) := by
  have hdreal : (100 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := by nlinarith
  have hlog_ge_one : 1 ≤ Real.log (d : ℝ) := by
    have hexp_le : Real.exp 1 ≤ (d : ℝ) := by
      have hexp_lt : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
      nlinarith
    rw [← Real.log_exp 1]
    exact Real.log_le_log (by positivity) hexp_le
  have hd2_ge_one : 1 ≤ (d : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1) (by nlinarith : (1 : ℝ) ≤ d) 2
    simpa using h
  have hd3_ge : (43 : ℝ) ≤ (d : ℝ) ^ 3 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (100 : ℝ)) hdreal 3
    norm_num at h
    nlinarith
  have hdiff_ge_one : 1 ≤ (d : ℝ) ^ 3 - 42 := by nlinarith
  have hcoef_ge_one : 1 ≤ (d : ℝ) ^ 5 - 42 * (d : ℝ) ^ 2 := by
    calc
      (1 : ℝ) ≤ (d : ℝ) ^ 2 * ((d : ℝ) ^ 3 - 42) := by
        nlinarith [
          mul_le_mul hd2_ge_one hdiff_ge_one (by nlinarith)
            (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 2)]
      _ = (d : ℝ) ^ 5 - 42 * (d : ℝ) ^ 2 := by ring
  have hgap : 1 ≤ ((d : ℝ) ^ 5 - 42 * (d : ℝ) ^ 2) * Real.log (d : ℝ) := by
    nlinarith [
      mul_le_mul hcoef_ge_one hlog_ge_one (by norm_num : (0 : ℝ) ≤ 1)
        (by nlinarith : 0 ≤ (d : ℝ) ^ 5 - 42 * (d : ℝ) ^ 2)]
  field_simp [ne_of_gt hdpos]
  ring_nf
  nlinarith


lemma eventually_twenty_six_log_le_nat :
    ∀ᶠ d : ℕ in Filter.atTop, (26 : ℝ) * Real.log (d : ℝ) ≤ (d : ℝ) := by
  have hreal : ∀ᶠ x : ℝ in Filter.atTop, (26 : ℝ) * Real.log x ≤ x := by
    have h := (Asymptotics.isLittleO_iff_nat_mul_le'.1 Real.isLittleO_log_id_atTop 26)
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hx_nonneg : 0 ≤ x := le_trans (by norm_num) hx1
    simpa [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hx_nonneg] using hx
  exact tendsto_natCast_atTop_atTop.eventually hreal

lemma seedIndepThreshold_le_d6_eventually :
    ∀ᶠ d : ℕ in Filter.atTop, seedIndepThreshold d ≤ d ^ 6 := by
  filter_upwards [eventually_twenty_six_log_le_nat,
    Filter.eventually_ge_atTop (2 : ℕ)] with d hlog hd
  have hk_lt := seedIndepThreshold_lt_add_one (by omega : 1 ≤ d)
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hd6_ge_two : (2 : ℝ) ≤ (d : ℝ) ^ 6 := by
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (2 : ℝ))
      (by exact_mod_cast hd : (2 : ℝ) ≤ d) 6
    norm_num at hpow
    nlinarith
  have hmain : 13 * (d : ℝ) ^ 5 * Real.log (d : ℝ) + 1 ≤ (d : ℝ) ^ 6 := by
    have hhalf : 13 * Real.log (d : ℝ) ≤ (d : ℝ) / 2 := by
      nlinarith
    have hmul : 13 * (d : ℝ) ^ 5 * Real.log (d : ℝ) ≤ ((d : ℝ) ^ 6) / 2 := by
      calc
        13 * (d : ℝ) ^ 5 * Real.log (d : ℝ) = (d : ℝ) ^ 5 * (13 * Real.log (d : ℝ)) := by ring
        _ ≤ (d : ℝ) ^ 5 * ((d : ℝ) / 2) := by
          exact mul_le_mul_of_nonneg_left hhalf (by positivity)
        _ = ((d : ℝ) ^ 6) / 2 := by ring
    nlinarith
  have hk_real : (seedIndepThreshold d : ℝ) ≤ (d ^ 6 : ℕ) := by
    exact_mod_cast (le_of_lt (hk_lt.trans_le hmain))
  exact_mod_cast hk_real

lemma seedIndepThreshold_slots_eventually :
    ∀ᶠ d : ℕ in Filter.atTop,
      (seedIndepThreshold d).choose 2 ≤ (d ^ 6).choose 2 := by
  filter_upwards [seedIndepThreshold_le_d6_eventually] with d hk
  exact Nat.choose_le_choose 2 hk

lemma seedIndepThreshold_alpha_le_survivors {d q : ℕ} (hq : 0 < q)
    (ω : Sample (d ^ 6) q) (hd : 100 ≤ d) (htri : triangleCount hq ω < d ^ 3) :
    (seedIndepThreshold d : ℝ) ≤
      14 * (Nat.card {v : Fin (d ^ 6) // v ∉ triangleVertices hq ω} : ℝ) *
        Real.log (d : ℝ) / (d : ℝ) := by
  have hk_lt := seedIndepThreshold_lt_add_one (by omega : 1 ≤ d)
  have hdel_lt : (triangleVertices hq ω).card < 3 * d ^ 3 := by
    have hdel_le := card_triangleVertices_le hq ω
    have htri3 : 3 * triangleCount hq ω < 3 * d ^ 3 := by
      exact Nat.mul_lt_mul_of_pos_left htri (by norm_num)
    exact lt_of_le_of_lt hdel_le htri3
  have hdel_le : (triangleVertices hq ω).card ≤ 3 * d ^ 3 := le_of_lt hdel_lt
  have hsurv_lower_nat : d ^ 6 - 3 * d ^ 3 ≤
      Nat.card {v : Fin (d ^ 6) // v ∉ triangleVertices hq ω} := by
    rw [natCard_survivors_triangleVertices hq ω]
    omega
  have hsub_le : 3 * d ^ 3 ≤ d ^ 6 := by
    have h3_le_d3 : 3 ≤ d ^ 3 := by
      have hpow := Nat.pow_le_pow_left (by omega : 2 ≤ d) 3
      norm_num at hpow
      omega
    have hd3_pos : 0 < d ^ 3 := by positivity
    calc
      3 * d ^ 3 ≤ d ^ 3 * d ^ 3 := Nat.mul_le_mul_right (d ^ 3) h3_le_d3
      _ = d ^ 6 := by ring
  have hsurv_lower_real :
      (d : ℝ) ^ 6 - 3 * (d : ℝ) ^ 3 ≤
        (Nat.card {v : Fin (d ^ 6) // v ∉ triangleVertices hq ω} : ℝ) := by
    have hcast : ((d ^ 6 - 3 * d ^ 3 : ℕ) : ℝ) =
        (d : ℝ) ^ 6 - 3 * (d : ℝ) ^ 3 := by
      rw [Nat.cast_sub hsub_le]
      norm_num
    have hrealcast : ((d ^ 6 - 3 * d ^ 3 : ℕ) : ℝ) ≤
        (Nat.card {v : Fin (d ^ 6) // v ∉ triangleVertices hq ω} : ℝ) := by
      exact_mod_cast hsurv_lower_nat
    rw [← hcast]
    exact hrealcast
  have hbudget := alpha_real_budget_aux hd
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hlog_nonneg : 0 ≤ Real.log (d : ℝ) := by
    have hlog_ge_one : 1 ≤ Real.log (d : ℝ) := by
      have hdreal : (100 : ℝ) ≤ d := by exact_mod_cast hd
      have hexp_le : Real.exp 1 ≤ (d : ℝ) := by
        have hexp_lt : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
        nlinarith
      rw [← Real.log_exp 1]
      exact Real.log_le_log (by positivity) hexp_le
    nlinarith
  have hmono :
      14 * (((d : ℝ) ^ 6 - 3 * (d : ℝ) ^ 3)) * Real.log (d : ℝ) / (d : ℝ) ≤
        14 * (Nat.card {v : Fin (d ^ 6) // v ∉ triangleVertices hq ω} : ℝ) *
          Real.log (d : ℝ) / (d : ℝ) := by
    gcongr
  exact (le_of_lt hk_lt).trans (hbudget.trans hmono)

lemma seedGraphOn_survivors_of_good_sample {N q d k : ℕ} (hq : 0 < q) (ω : Sample N q)
    (hd : 3 ≤ d)
    (hdeg : highDegWitnessCount hq d ω = 0)
    (hindep : indepWitnessCount hq k ω = 0)
    (halpha : (k : ℝ) ≤
      14 * (Nat.card {v : Fin N // v ∉ triangleVertices hq ω} : ℝ) *
        Real.log (d : ℝ) / (d : ℝ)) :
    SeedGraphOn d ((graphOf hq ω).induce {v : Fin N | v ∉ triangleVertices hq ω}) := by
  classical
  constructor
  · exact cliqueFree_induce_compl_triangleVertices hq ω
  constructor
  · intro v
    have hbase := degree_add_three_le_of_highDegWitnessCount_eq_zero hq ω hd hdeg v.1
    have hle := neighborSet_ncard_induce_le (graphOf hq ω)
      ({v : Fin N | v ∉ triangleVertices hq ω}) v
    omega
  · have hnat :
        ((graphOf hq ω).induce {v : Fin N | v ∉ triangleVertices hq ω}).indepNum < k := by
      exact lt_of_le_of_lt
        (indepNum_induce_le (graphOf hq ω) ({v : Fin N | v ∉ triangleVertices hq ω}))
        (indepNum_lt_of_indepWitnessCount_eq_zero hq ω hindep)
    exact (Nat.cast_lt.mpr hnat).le.trans halpha



lemma highDeg_param_moment_bound_of_cancelled {d : ℕ} (hdpos : 0 < d)
    (hslots : d - 3 ≤ (d ^ 6).choose 2)
    (h : 3 * ((d ^ 6) * (d ^ 6).choose (d - 3)) <
      (6 * d ^ 5) ^ (d - 3)) :
    3 * (((d ^ 6) * (d ^ 6).choose (d - 3)) *
        (6 * d ^ 5) ^ ((d ^ 6).choose 2 - (d - 3))) <
      (6 * d ^ 5) ^ (d ^ 6).choose 2 := by
  have hqpos : 0 < 6 * d ^ 5 := by positivity
  have hApos : 0 < (6 * d ^ 5) ^ ((d ^ 6).choose 2 - (d - 3)) := by positivity
  have hsplit :
      (6 * d ^ 5) ^ (d ^ 6).choose 2 =
        (6 * d ^ 5) ^ ((d ^ 6).choose 2 - (d - 3)) *
          (6 * d ^ 5) ^ (d - 3) := by
    rw [← pow_add, Nat.sub_add_cancel hslots]
  have hmul := Nat.mul_lt_mul_of_pos_right h hApos
  rw [hsplit]
  nlinarith

lemma indep_param_moment_bound_of_cancelled {d k : ℕ} (hdpos : 0 < d)
    (hslots : k.choose 2 ≤ (d ^ 6).choose 2)
    (h : 3 * ((d ^ 6).choose k * ((6 * d ^ 5 - 1) ^ (k.choose 2))) <
      (6 * d ^ 5) ^ (k.choose 2)) :
    3 * ((d ^ 6).choose k *
        (((6 * d ^ 5) - 1) ^ (k.choose 2) *
          (6 * d ^ 5) ^ ((d ^ 6).choose 2 - k.choose 2))) <
      (6 * d ^ 5) ^ (d ^ 6).choose 2 := by
  have hqpos : 0 < 6 * d ^ 5 := by positivity
  have hApos : 0 < (6 * d ^ 5) ^ ((d ^ 6).choose 2 - k.choose 2) := by positivity
  have hsplit :
      (6 * d ^ 5) ^ (d ^ 6).choose 2 =
        (6 * d ^ 5) ^ ((d ^ 6).choose 2 - k.choose 2) *
          (6 * d ^ 5) ^ (k.choose 2) := by
    rw [← pow_add, Nat.sub_add_cancel hslots]
  have hmul := Nat.mul_lt_mul_of_pos_right h hApos
  rw [hsplit]
  nlinarith



lemma highDeg_slots_param_le {d : ℕ} (hd : 2 ≤ d) :
    d - 3 ≤ (d ^ 6).choose 2 := by
  have hd_le_pow : d ≤ d ^ 6 := by
    exact Nat.le_self_pow (n := 6) (Nat.ne_of_gt (by norm_num : 0 < 6)) d
  have hN : 3 ≤ d ^ 6 := by
    have hpow := Nat.pow_le_pow_left hd 6
    norm_num at hpow
    omega
  have hchoose_ge : d ^ 6 ≤ (d ^ 6).choose 2 := by
    rw [Nat.choose_two_right]
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have hNm1 : 2 ≤ d ^ 6 - 1 := by omega
    exact Nat.mul_le_mul_left (d ^ 6) hNm1
  omega

lemma exists_sample_of_param_cancelled_bounds {d k : ℕ} (hd : 2 ≤ d)
    (hdegSlots : d - 3 ≤ (d ^ 6).choose 2)
    (hindepSlots : k.choose 2 ≤ (d ^ 6).choose 2)
    (hdeg : 3 * ((d ^ 6) * (d ^ 6).choose (d - 3)) <
      (6 * d ^ 5) ^ (d - 3))
    (hindep : 3 * ((d ^ 6).choose k * ((6 * d ^ 5 - 1) ^ (k.choose 2))) <
      (6 * d ^ 5) ^ (k.choose 2)) :
    ∃ ω : Sample (d ^ 6) (6 * d ^ 5),
      highDegWitnessCount (by positivity) d ω = 0 ∧
        indepWitnessCount (by positivity) k ω = 0 ∧ triangleCount (by positivity) ω < d ^ 3 := by
  have hdpos : 0 < d := by omega
  exact exists_sample_of_param_moment_bounds hd
    (highDeg_param_moment_bound_of_cancelled hdpos hdegSlots hdeg)
    (indep_param_moment_bound_of_cancelled hdpos hindepSlots hindep)



lemma exists_sample_of_param_cancelled_bounds' {d k : ℕ} (hd : 2 ≤ d)
    (hindepSlots : k.choose 2 ≤ (d ^ 6).choose 2)
    (hdeg : 3 * ((d ^ 6) * (d ^ 6).choose (d - 3)) <
      (6 * d ^ 5) ^ (d - 3))
    (hindep : 3 * ((d ^ 6).choose k * ((6 * d ^ 5 - 1) ^ (k.choose 2))) <
      (6 * d ^ 5) ^ (k.choose 2)) :
    ∃ ω : Sample (d ^ 6) (6 * d ^ 5),
      highDegWitnessCount (by positivity) d ω = 0 ∧
        indepWitnessCount (by positivity) k ω = 0 ∧ triangleCount (by positivity) ω < d ^ 3 := by
  exact exists_sample_of_param_cancelled_bounds hd (highDeg_slots_param_le hd)
    hindepSlots hdeg hindep

lemma real_pow_div_three_le_factorial (n : ℕ) :
    ((n : ℝ) / 3) ^ n ≤ (Nat.factorial n : ℝ) := by
  rcases n with _ | n
  · norm_num
  · have hdiv : ((n.succ : ℝ) / 3) ≤ ((n.succ : ℝ) / Real.exp 1) := by
      gcongr
      exact Real.exp_one_lt_three.le
    have hpow : ((n.succ : ℝ) / 3) ^ n.succ ≤
        ((n.succ : ℝ) / Real.exp 1) ^ n.succ := by
      exact pow_le_pow_left₀ (by positivity) hdiv n.succ
    have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (n.succ : ℝ)) := by
      rw [Real.one_le_sqrt]
      have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hn : (1 : ℝ) ≤ n.succ := by exact_mod_cast Nat.succ_pos n
      nlinarith
    calc
      ((n.succ : ℝ) / 3) ^ n.succ ≤
          ((n.succ : ℝ) / Real.exp 1) ^ n.succ := hpow
      _ ≤ Real.sqrt (2 * Real.pi * (n.succ : ℝ)) *
          ((n.succ : ℝ) / Real.exp 1) ^ n.succ := by
        nth_rewrite 1 [← one_mul (((n.succ : ℝ) / Real.exp 1) ^ n.succ)]
        exact mul_le_mul_of_nonneg_right hsqrt (by positivity)
      _ ≤ (Nat.factorial n.succ : ℝ) := Stirling.le_factorial_stirling n.succ


lemma choose_le_three_mul_pow_div {N k : ℕ} (hk : 0 < k) :
    (N.choose k : ℝ) ≤ (3 * (N : ℝ) / (k : ℝ)) ^ k := by
  have hchoose₁ : (N.choose k : ℝ) ≤ ((N : ℝ) ^ k) / (Nat.factorial k : ℝ) := by
    exact Nat.choose_le_pow_div (α := ℝ) k N
  have hfact : ((k : ℝ) / 3) ^ k ≤ (Nat.factorial k : ℝ) :=
    real_pow_div_three_le_factorial k
  have hdenpos : 0 < ((k : ℝ) / 3) ^ k := by positivity
  have hchoose₂ : (N.choose k : ℝ) ≤ ((N : ℝ) ^ k) / (((k : ℝ) / 3) ^ k) := by
    exact hchoose₁.trans (div_le_div_of_nonneg_left (by positivity) hdenpos hfact)
  have hratio_eq : ((N : ℝ) ^ k) / (((k : ℝ) / 3) ^ k) =
      (3 * (N : ℝ) / (k : ℝ)) ^ k := by
    have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hk
    rw [div_pow, div_pow, mul_pow]
    field_simp [pow_ne_zero k hkreal]
  exact hchoose₂.trans_eq hratio_eq

lemma highDeg_cancelled_bound_of_exp_poly {d : ℕ} (hd : 12 ≤ d)
    (hpoly : 2 ^ (d - 3) * (3 * d ^ 6) < 3 ^ (d - 3)) :
    3 * ((d ^ 6) * (d ^ 6).choose (d - 3)) < (6 * d ^ 5) ^ (d - 3) := by
  let r := d - 3
  have hrpos_nat : 0 < r := by omega
  have hchoose₁ : (((d ^ 6).choose r : ℕ) : ℝ) ≤
      (((d ^ 6 : ℕ) : ℝ) ^ r) / (Nat.factorial r : ℝ) := by
    exact Nat.choose_le_pow_div (α := ℝ) r (d ^ 6)
  have hfact : ((r : ℝ) / 3) ^ r ≤ (Nat.factorial r : ℝ) :=
    real_pow_div_three_le_factorial r
  have hdenpos : 0 < ((r : ℝ) / 3) ^ r := by positivity
  have hchoose₂ : (((d ^ 6).choose r : ℕ) : ℝ) ≤
      (((d ^ 6 : ℕ) : ℝ) ^ r) / (((r : ℝ) / 3) ^ r) := by
    exact hchoose₁.trans (div_le_div_of_nonneg_left (by positivity) hdenpos hfact)
  have hratio_eq :
      (((d ^ 6 : ℕ) : ℝ) ^ r) / (((r : ℝ) / 3) ^ r) =
        (3 * ((d ^ 6 : ℕ) : ℝ) / (r : ℝ)) ^ r := by
    have hrne : (r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hrpos_nat
    rw [div_pow, div_pow, mul_pow]
    field_simp [pow_ne_zero r hrne]
  have hratio_le : 3 * ((d ^ 6 : ℕ) : ℝ) / (r : ℝ) ≤ 4 * (d : ℝ) ^ 5 := by
    have hdreal : (12 : ℝ) ≤ d := by exact_mod_cast hd
    have hr_eq : (r : ℝ) = (d : ℝ) - 3 := by
      simp [r, Nat.cast_sub (by omega : 3 ≤ d)]
    rw [show (((d ^ 6 : ℕ) : ℝ)) = (d : ℝ) ^ 6 by norm_num]
    rw [hr_eq]
    rw [div_le_iff₀ (show 0 < (d : ℝ) - 3 by nlinarith)]
    have hnonneg : 0 ≤ (d : ℝ) ^ 5 * ((d : ℝ) - 12) := by
      exact mul_nonneg (by positivity) (sub_nonneg.mpr hdreal)
    nlinarith
  have hchoose₃ : (((d ^ 6).choose r : ℕ) : ℝ) ≤ (4 * (d : ℝ) ^ 5) ^ r := by
    calc
      (((d ^ 6).choose r : ℕ) : ℝ) ≤
          (((d ^ 6 : ℕ) : ℝ) ^ r) / (((r : ℝ) / 3) ^ r) := hchoose₂
      _ = (3 * ((d ^ 6 : ℕ) : ℝ) / (r : ℝ)) ^ r := hratio_eq
      _ ≤ (4 * (d : ℝ) ^ 5) ^ r := pow_le_pow_left₀ (by positivity) hratio_le r
  have hpoly_real : (2 : ℝ) ^ r * (3 * (d : ℝ) ^ 6) < (3 : ℝ) ^ r := by
    have hp : ((2 ^ r * (3 * d ^ 6) : ℕ) : ℝ) < ((3 ^ r : ℕ) : ℝ) := by
      exact_mod_cast (by simpa [r] using hpoly)
    simpa using hp
  have hcoeff : 3 * (d : ℝ) ^ 6 * (4 * (d : ℝ) ^ 5) ^ r < (6 * (d : ℝ) ^ 5) ^ r := by
    have hmul := mul_lt_mul_of_pos_left hpoly_real
      (show 0 < (2 : ℝ) ^ r * ((d : ℝ) ^ 5) ^ r by positivity)
    rw [mul_assoc] at hmul
    calc
      3 * (d : ℝ) ^ 6 * (4 * (d : ℝ) ^ 5) ^ r
          = ((2 : ℝ) ^ r * ((d : ℝ) ^ 5) ^ r) * ((2 : ℝ) ^ r * (3 * (d : ℝ) ^ 6)) := by
            rw [show (4 : ℝ) = 2 * 2 by norm_num]
            rw [mul_pow, mul_pow]
            ring
      _ < ((2 : ℝ) ^ r * ((d : ℝ) ^ 5) ^ r) * (3 : ℝ) ^ r := by
        simpa [mul_assoc] using hmul
      _ = (6 * (d : ℝ) ^ 5) ^ r := by
        rw [show (6 : ℝ) = 2 * 3 by norm_num]
        rw [mul_pow, mul_pow]
        ring
  have hreal : (3 * ((d ^ 6) * (d ^ 6).choose (d - 3)) : ℝ) <
      ((6 * d ^ 5) ^ (d - 3) : ℝ) := by
    have hmulchoose : (3 * (d : ℝ) ^ 6) * (((d ^ 6).choose r : ℕ) : ℝ) ≤
        (3 * (d : ℝ) ^ 6) * (4 * (d : ℝ) ^ 5) ^ r := by
      exact mul_le_mul_of_nonneg_left hchoose₃ (by positivity)
    calc
      (3 * ((d ^ 6) * (d ^ 6).choose (d - 3)) : ℝ)
          = (3 * (d : ℝ) ^ 6) * (((d ^ 6).choose r : ℕ) : ℝ) := by
            simp [r]
            ring
      _ ≤ (3 * (d : ℝ) ^ 6) * (4 * (d : ℝ) ^ 5) ^ r := hmulchoose
      _ = 3 * (d : ℝ) ^ 6 * (4 * (d : ℝ) ^ 5) ^ r := by ring
      _ < (6 * (d : ℝ) ^ 5) ^ r := hcoeff
      _ = ((6 * d ^ 5) ^ (d - 3) : ℝ) := by
        simp [r]
  exact_mod_cast hreal


lemma poly_step_two_three {d : ℕ} (hd : 20 ≤ d) :
    2 * (d + 1) ^ 6 ≤ 3 * d ^ 6 := by
  have hreal : (2 * ((d + 1 : ℕ) : ℝ) ^ 6) ≤ (3 * (d : ℝ) ^ 6) := by
    have hdreal : (20 : ℝ) ≤ d := by exact_mod_cast hd
    have hle : ((d + 1 : ℕ) : ℝ) ≤ (21 / 20 : ℝ) * d := by
      norm_num
      nlinarith
    have hpow : ((d + 1 : ℕ) : ℝ) ^ 6 ≤ ((21 / 20 : ℝ) * d) ^ 6 := by
      exact pow_le_pow_left₀ (by positivity) hle 6
    have hmul : 2 * ((d + 1 : ℕ) : ℝ) ^ 6 ≤ 2 * (((21 / 20 : ℝ) * d) ^ 6) := by
      exact mul_le_mul_of_nonneg_left hpow (by norm_num)
    have hcoef : 2 * (((21 / 20 : ℝ) * d) ^ 6) ≤ 3 * (d : ℝ) ^ 6 := by
      calc
        2 * (((21 / 20 : ℝ) * d) ^ 6) =
            (2 * (21 / 20 : ℝ) ^ 6) * (d : ℝ) ^ 6 := by ring
        _ ≤ 3 * (d : ℝ) ^ 6 := by
          exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    exact hmul.trans hcoef
  exact_mod_cast hreal

lemma two_three_pow_dom_poly_aux :
    ∀ d : ℕ, 100 ≤ d → 2 ^ (d - 3) * (3 * d ^ 6) < 3 ^ (d - 3)
  | 0, h => by omega
  | d + 1, h => by
      by_cases hd100 : 100 ≤ d
      · have ih := two_three_pow_dom_poly_aux d hd100
        have hstep : 2 * (d + 1) ^ 6 ≤ 3 * d ^ 6 :=
          poly_step_two_three (by omega : 20 ≤ d)
        have hstep' : 2 * (3 * (d + 1) ^ 6) ≤ 3 * (3 * d ^ 6) := by
          nlinarith
        have hleft_le :
            2 * (2 ^ (d - 3) * (3 * (d + 1) ^ 6)) ≤
              3 * (2 ^ (d - 3) * (3 * d ^ 6)) := by
          have hmul := Nat.mul_le_mul_left (2 ^ (d - 3)) hstep'
          nlinarith
        have hleft_eq :
            2 ^ (d + 1 - 3) * (3 * (d + 1) ^ 6) =
              2 * (2 ^ (d - 3) * (3 * (d + 1) ^ 6)) := by
          have hexp : d + 1 - 3 = (d - 3) + 1 := by omega
          rw [hexp, pow_succ]
          ring
        have hright_eq : 3 ^ (d + 1 - 3) = 3 * 3 ^ (d - 3) := by
          have hexp : d + 1 - 3 = (d - 3) + 1 := by omega
          rw [hexp, pow_succ]
          ring
        rw [hleft_eq, hright_eq]
        exact lt_of_le_of_lt hleft_le (Nat.mul_lt_mul_of_pos_left ih (by norm_num))
      · have hd : d = 99 := by omega
        subst d
        norm_num

lemma highDeg_cancelled_bound_eventually :
    ∀ᶠ d : ℕ in Filter.atTop,
      3 * ((d ^ 6) * (d ^ 6).choose (d - 3)) < (6 * d ^ 5) ^ (d - 3) := by
  filter_upwards [Filter.eventually_ge_atTop (100 : ℕ)] with d hd
  exact highDeg_cancelled_bound_of_exp_poly (by omega : 12 ≤ d)
    (two_three_pow_dom_poly_aux d hd)


lemma graph_degree_and_indep_of_good_sample {N q d k : ℕ} (hq : 0 < q)
    (ω : Sample N q) (hd : 3 ≤ d)
    (hdeg : highDegWitnessCount hq d ω = 0)
    (hindep : indepWitnessCount hq k ω = 0) :
    (∀ v : Fin N, ((graphOf hq ω).neighborSet v).ncard + 3 ≤ d) ∧
      (graphOf hq ω).indepNum < k :=
  ⟨degree_add_three_le_of_highDegWitnessCount_eq_zero hq ω hd hdeg,
    indepNum_lt_of_indepWitnessCount_eq_zero hq ω hindep⟩

lemma not_ordered_triangle_of_triangleCount_eq_zero {N q : ℕ} (hq : 0 < q)
    (ω : Sample N q) (hzero : triangleCount hq ω = 0)
    {u v w : Fin N} (huv : u < v) (hvw : v < w) :
    ¬ ((graphOf hq ω).Adj u v ∧ (graphOf hq ω).Adj v w ∧
      (graphOf hq ω).Adj u w) := by
  intro htri
  let T : TriangleWitness N := ⟨(u, v, w), huv, hvw⟩
  have hbad := (triangleCount_eq_zero_iff hq ω).1 hzero T
  apply hbad
  constructor
  · have hne : u ≠ v := ne_of_lt huv
    simpa [T, slotOf_of_lt hne huv] using (graphOf_adj_iff_slot hq ω hne).1 htri.1
  constructor
  · have hne : v ≠ w := ne_of_lt hvw
    simpa [T, slotOf_of_lt hne hvw] using (graphOf_adj_iff_slot hq ω hne).1 htri.2.1
  · have huw : u < w := huv.trans hvw
    have hne : u ≠ w := ne_of_lt huw
    simpa [T, slotOf_of_lt hne huw] using (graphOf_adj_iff_slot hq ω hne).1 htri.2.2



lemma ratio_pow_le_exp_neg {q r : ℕ} (hq : 1 ≤ q) :
    (((q - 1 : ℕ) : ℝ) / (q : ℝ)) ^ r ≤ Real.exp (-(r : ℝ) / (q : ℝ)) := by
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hq)
  have hratio_eq : (((q - 1 : ℕ) : ℝ) / (q : ℝ)) = 1 - (q : ℝ)⁻¹ := by
    rw [Nat.cast_sub hq]
    norm_num
    field_simp [ne_of_gt hqpos]
  have hbase_nonneg : 0 ≤ 1 - (q : ℝ)⁻¹ := by
    rw [sub_nonneg]
    rw [inv_le_one₀ hqpos]
    exact_mod_cast hq
  calc
    (((q - 1 : ℕ) : ℝ) / (q : ℝ)) ^ r = (1 - (q : ℝ)⁻¹) ^ r := by rw [hratio_eq]
    _ ≤ (Real.exp (-(q : ℝ)⁻¹)) ^ r :=
      pow_le_pow_left₀ hbase_nonneg (Real.one_sub_le_exp_neg ((q : ℝ)⁻¹)) r
    _ = Real.exp (-(r : ℝ) / (q : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp [ne_of_gt hqpos]

lemma indep_cancelled_bound_of_ratio {N q k : ℕ} (hq : 0 < q)
    (h : (3 : ℝ) * (N.choose k : ℝ) *
        ((((q - 1 : ℕ) : ℝ) / (q : ℝ)) ^ (k.choose 2)) < 1) :
    3 * (N.choose k * ((q - 1) ^ (k.choose 2))) < q ^ (k.choose 2) := by
  let r := k.choose 2
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqpowpos : 0 < (q : ℝ) ^ r := by positivity
  have hmul := mul_lt_mul_of_pos_right h hqpowpos
  have hratio_mul : ((((q - 1 : ℕ) : ℝ) / (q : ℝ)) ^ r) * (q : ℝ) ^ r =
      ((q - 1 : ℕ) : ℝ) ^ r := by
    rw [div_pow]
    field_simp [ne_of_gt hqpos]
  have hleft_eq :
      ((3 : ℝ) * (N.choose k : ℝ) *
          ((((q - 1 : ℕ) : ℝ) / (q : ℝ)) ^ r)) * (q : ℝ) ^ r =
        ((3 * (N.choose k * ((q - 1) ^ r)) : ℕ) : ℝ) := by
    rw [mul_assoc, hratio_mul]
    norm_num
    ring
  have hreal : ((3 * (N.choose k * ((q - 1) ^ r)) : ℕ) : ℝ) < ((q ^ r : ℕ) : ℝ) := by
    rw [← hleft_eq]
    simpa [r] using hmul
  exact_mod_cast hreal


lemma indep_ratio_bound_of_exp_estimate {N q k : ℕ} (hk : 0 < k) (hq : 1 ≤ q)
    (h : (3 : ℝ) * (3 * (N : ℝ) / (k : ℝ)) ^ k *
        Real.exp (-((k.choose 2 : ℕ) : ℝ) / (q : ℝ)) < 1) :
    (3 : ℝ) * (N.choose k : ℝ) *
        ((((q - 1 : ℕ) : ℝ) / (q : ℝ)) ^ (k.choose 2)) < 1 := by
  calc
    (3 : ℝ) * (N.choose k : ℝ) *
        ((((q - 1 : ℕ) : ℝ) / (q : ℝ)) ^ (k.choose 2))
        ≤ 3 * (3 * (N : ℝ) / (k : ℝ)) ^ k *
            ((((q - 1 : ℕ) : ℝ) / (q : ℝ)) ^ (k.choose 2)) := by
          gcongr
          exact choose_le_three_mul_pow_div hk
    _ ≤ 3 * (3 * (N : ℝ) / (k : ℝ)) ^ k *
            Real.exp (-((k.choose 2 : ℕ) : ℝ) / (q : ℝ)) := by
          gcongr
          exact ratio_pow_le_exp_neg hq
    _ < 1 := h


lemma exp_power_estimate_of_log_neg {A B : ℝ} {k : ℕ} (hA : 0 < A)
    (h : Real.log 3 + (k : ℝ) * Real.log A - B < 0) :
    (3 : ℝ) * A ^ k * Real.exp (-B) < 1 := by
  have h_eq : (3 : ℝ) * A ^ k * Real.exp (-B) =
      Real.exp (Real.log 3 + (k : ℝ) * Real.log A - B) := by
    rw [Real.exp_sub, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    rw [Real.exp_nat_mul, Real.exp_log hA, Real.exp_neg]
    ring_nf
  rw [h_eq]
  simpa using (Real.exp_lt_exp.mpr h)

/-- Final logarithmic calculus estimate left for the finite-counting independence bound. -/
lemma indep_log_estimate_eventually :
    ∀ᶠ d : ℕ in Filter.atTop,
      Real.log 3 + (seedIndepThreshold d : ℝ) *
          Real.log (3 * ((d ^ 6 : ℕ) : ℝ) / (seedIndepThreshold d : ℝ)) -
        (((seedIndepThreshold d).choose 2 : ℕ) : ℝ) / ((6 * d ^ 5 : ℕ) : ℝ) < 0 := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (13 : ℝ)] with d hd hlog13
  let k := seedIndepThreshold d
  let L := Real.log (d : ℝ)
  have hdpos_nat : 0 < d := by omega
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hdpos_nat
  have hd5pos : 0 < (d : ℝ) ^ 5 := by positivity
  have hd5nonneg : 0 ≤ (d : ℝ) ^ 5 := by positivity
  have hd5ge1 : 1 ≤ (d : ℝ) ^ 5 := by
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (1 : ℝ))
      (by exact_mod_cast hd : (1 : ℝ) ≤ d) 5
    simpa using hpow
  have hL13 : (13 : ℝ) ≤ L := by simpa [L] using hlog13
  have hLpos : 0 < L := by nlinarith
  have hk_ge : 13 * (d : ℝ) ^ 5 * L ≤ (k : ℝ) := by
    simpa [k, L] using seedIndepThreshold_ge d
  have hkpos : 0 < (k : ℝ) := by
    have : 0 < 13 * (d : ℝ) ^ 5 * L := by positivity
    exact lt_of_lt_of_le this hk_ge
  have hk_nonneg : 0 ≤ (k : ℝ) := le_of_lt hkpos
  have hApos : 0 < 3 * ((d ^ 6 : ℕ) : ℝ) / (k : ℝ) := by positivity
  have h3d5_le_k : 3 * (d : ℝ) ^ 5 ≤ (k : ℝ) := by
    have hcoef : (3 : ℝ) ≤ 13 * L := by nlinarith
    have hbase : 3 * (d : ℝ) ^ 5 ≤ 13 * (d : ℝ) ^ 5 * L := by
      nlinarith [mul_le_mul_of_nonneg_right hcoef hd5nonneg]
    exact hbase.trans hk_ge
  have hA_le_d : 3 * ((d ^ 6 : ℕ) : ℝ) / (k : ℝ) ≤ (d : ℝ) := by
    rw [div_le_iff₀ hkpos]
    have hmul := mul_le_mul_of_nonneg_left h3d5_le_k (le_of_lt hdpos)
    calc
      3 * ((d ^ 6 : ℕ) : ℝ) = (d : ℝ) * (3 * (d : ℝ) ^ 5) := by
        norm_num
        ring
      _ ≤ (d : ℝ) * (k : ℝ) := hmul
  have hlogA_le : Real.log (3 * ((d ^ 6 : ℕ) : ℝ) / (k : ℝ)) ≤ L := by
    simpa [L] using Real.log_le_log hApos hA_le_d
  have hpos_part : (k : ℝ) * Real.log (3 * ((d ^ 6 : ℕ) : ℝ) / (k : ℝ)) ≤ (k : ℝ) * L := by
    exact mul_le_mul_of_nonneg_left hlogA_le hk_nonneg
  have hfactor_num : 12 * (d : ℝ) ^ 5 * (L + 1) ≤ (k : ℝ) - 1 := by
    have hneed : 12 * (d : ℝ) ^ 5 + 1 ≤ (d : ℝ) ^ 5 * L := by
      have h13mul : 13 * (d : ℝ) ^ 5 ≤ (d : ℝ) ^ 5 * L := by
        nlinarith [mul_le_mul_of_nonneg_left hL13 hd5nonneg]
      nlinarith
    nlinarith
  have hfactor : L + 1 ≤ ((k : ℝ) - 1) / (12 * (d : ℝ) ^ 5) := by
    rw [le_div_iff₀ (by positivity : 0 < 12 * (d : ℝ) ^ 5)]
    nlinarith
  have hchoose_eq : (((k.choose 2 : ℕ) : ℝ) / ((6 * d ^ 5 : ℕ) : ℝ)) =
      (k : ℝ) * (((k : ℝ) - 1) / (12 * (d : ℝ) ^ 5)) := by
    rw [Nat.cast_choose_two]
    norm_num
    field_simp [ne_of_gt hdpos]
    ring
  have hneg_lower : (k : ℝ) * (L + 1) ≤
      (((k.choose 2 : ℕ) : ℝ) / ((6 * d ^ 5 : ℕ) : ℝ)) := by
    rw [hchoose_eq]
    exact mul_le_mul_of_nonneg_left hfactor hk_nonneg
  have hlog3_lt_k : Real.log 3 < (k : ℝ) := by
    have hlog3_le : Real.log 3 ≤ (3 : ℝ) := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 3)
    have hk_large : (169 : ℝ) ≤ (k : ℝ) := by
      have hprod : (13 : ℝ) ≤ (d : ℝ) ^ 5 * L := by
        exact le_trans (by norm_num : (13 : ℝ) ≤ 1 * 13) <|
          mul_le_mul hd5ge1 hL13 (by norm_num : (0 : ℝ) ≤ 13) hd5nonneg
      have hbase : (169 : ℝ) ≤ 13 * (d : ℝ) ^ 5 * L := by nlinarith
      exact hbase.trans hk_ge
    nlinarith
  have hmain : Real.log 3 + (k : ℝ) * Real.log (3 * ((d ^ 6 : ℕ) : ℝ) / (k : ℝ)) <
      (((k.choose 2 : ℕ) : ℝ) / ((6 * d ^ 5 : ℕ) : ℝ)) := by
    have hupper : Real.log 3 + (k : ℝ) * Real.log (3 * ((d ^ 6 : ℕ) : ℝ) / (k : ℝ)) ≤
        Real.log 3 + (k : ℝ) * L := by nlinarith
    have hlower : (k : ℝ) * L + (k : ℝ) ≤
        (((k.choose 2 : ℕ) : ℝ) / ((6 * d ^ 5 : ℕ) : ℝ)) := by
      nlinarith
    nlinarith
  simpa [k, L, sub_lt_iff_lt_add] using hmain
/-- Exponential form of the finite-counting independence estimate. -/
lemma indep_exp_estimate_eventually :
    ∀ᶠ d : ℕ in Filter.atTop,
      (3 : ℝ) * (3 * ((d ^ 6 : ℕ) : ℝ) / (seedIndepThreshold d : ℝ)) ^
          (seedIndepThreshold d) *
        Real.exp (-(((seedIndepThreshold d).choose 2 : ℕ) : ℝ) /
          ((6 * d ^ 5 : ℕ) : ℝ)) < 1 := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), seedIndepThreshold_pos_eventually,
    indep_log_estimate_eventually] with d hd hk hlog
  have hA : 0 < 3 * ((d ^ 6 : ℕ) : ℝ) / (seedIndepThreshold d : ℝ) := by
    positivity
  simpa [neg_div] using exp_power_estimate_of_log_neg (A := 3 * ((d ^ 6 : ℕ) : ℝ) /
    (seedIndepThreshold d : ℝ)) hA hlog

/-- Pure-real independence estimate for the finite-counting seed. -/
lemma indep_ratio_bound_eventually :
    ∀ᶠ d : ℕ in Filter.atTop,
      (3 : ℝ) * ((d ^ 6).choose (seedIndepThreshold d) : ℝ) *
          ((((6 * d ^ 5 - 1 : ℕ) : ℝ) / ((6 * d ^ 5 : ℕ) : ℝ)) ^
            ((seedIndepThreshold d).choose 2)) < 1 := by
  filter_upwards [seedIndepThreshold_pos_eventually, Filter.eventually_ge_atTop (1 : ℕ),
    indep_exp_estimate_eventually] with d hk hd h
  exact indep_ratio_bound_of_exp_estimate (N := d ^ 6) (q := 6 * d ^ 5)
    (k := seedIndepThreshold d) hk (by
      have hd5 : 1 ≤ d ^ 5 := by
        have hpow := Nat.pow_le_pow_left hd 5
        norm_num at hpow
        exact hpow
      omega) h

/-- Natural-number form of the remaining independence moment estimate. -/
lemma indep_cancelled_bound_eventually :
    ∀ᶠ d : ℕ in Filter.atTop,
      3 * ((d ^ 6).choose (seedIndepThreshold d) *
          ((6 * d ^ 5 - 1) ^ ((seedIndepThreshold d).choose 2))) <
        (6 * d ^ 5) ^ ((seedIndepThreshold d).choose 2) := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), indep_ratio_bound_eventually] with d hd h
  exact indep_cancelled_bound_of_ratio (N := d ^ 6) (q := 6 * d ^ 5)
    (k := seedIndepThreshold d) (by positivity) h

/-- Finite counting output from the witness-count strategy in `update2.md`.

The intended proof now asks for zero high-degree witnesses, zero independent-set witnesses, and at
most `d ^ 3` triangle witnesses.  High-degree vertices no longer need to be deleted; only triangle
vertices are removed before inducing the survivor graph. -/
theorem good_seed_graph_on_exists :
    ∀ᶠ d : ℕ in Filter.atTop,
      ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V) (G : SimpleGraph V),
        SeedGraphOn d G := by
  filter_upwards [Filter.eventually_ge_atTop (100 : ℕ), highDeg_cancelled_bound_eventually,
    seedIndepThreshold_slots_eventually, indep_cancelled_bound_eventually] with
    d hd hdeg hslots hindep
  let hq : 0 < 6 * d ^ 5 := by positivity
  let k := seedIndepThreshold d
  rcases exists_sample_of_param_cancelled_bounds' (d := d) (k := k) (by omega : 2 ≤ d)
      hslots hdeg (by simpa [k] using hindep) with ⟨ω, hdeg0, hindep0, htri⟩
  let V := {v : Fin (d ^ 6) // v ∉ triangleVertices hq ω}
  have hVne : Nonempty V := by
    exact nonempty_survivors_of_triangle_bound hq ω (by omega : 2 ≤ d) htri
  refine ⟨V, inferInstance, hVne,
    (graphOf hq ω).induce {v : Fin (d ^ 6) | v ∉ triangleVertices hq ω}, ?_⟩
  have halpha : (k : ℝ) ≤
      14 * (Nat.card {v : Fin (d ^ 6) // v ∉ triangleVertices hq ω} : ℝ) *
        Real.log (d : ℝ) / (d : ℝ) := by
    change (seedIndepThreshold d : ℝ) ≤
      14 * (Nat.card {v : Fin (d ^ 6) // v ∉ triangleVertices hq ω} : ℝ) *
        Real.log (d : ℝ) / (d : ℝ)
    exact seedIndepThreshold_alpha_le_survivors hq ω hd htri
  exact seedGraphOn_survivors_of_good_sample hq ω (by omega : 3 ≤ d) hdeg0 hindep0 halpha

/-- Modified seed existence from the finite counting output. -/
theorem seed_graph_exists :
    ∀ᶠ d : ℕ in Filter.atTop,
      ∃ n₀ : ℕ, 0 < n₀ ∧ ∃ G : SimpleGraph (Fin n₀), SeedGraph d n₀ G := by
  filter_upwards [good_seed_graph_on_exists] with d h
  rcases h with ⟨V, hV, hVne, G, hG⟩
  letI : Fintype V := hV
  letI : Nonempty V := hVne
  rcases seedGraph_of_seedGraphOn (d := d) (G := G) hG with ⟨H, hH⟩
  refine ⟨Fintype.card V, Fintype.card_pos, H, hH⟩

end SeedCounting

/-- Probabilistic seed existence promised by Lemma E1 in `lemmae.md`.

This is the first non-mathlib gap in the attempted proof.  Mathlib has `PMF.binomial`, general
Chernoff/MGF tools, and Markov inequalities, but I did not find a ready-made Erdos-Renyi random
graph construction with the degree, independence, and triangle-count estimates needed here. -/
theorem seed_graph_exists :
    ∀ᶠ d : ℕ in Filter.atTop,
      ∃ n₀ : ℕ, 0 < n₀ ∧ ∃ G : SimpleGraph (Fin n₀), SeedGraph d n₀ G := by
  exact SeedCounting.seed_graph_exists

namespace Gluing

lemma decomp_unique {a x y i j : ℕ} (hi : i < a) (hj : j < a)
    (h : a * x + i = a * y + j) : x = y ∧ i = j := by
  have ha : 0 < a := by omega
  have hmod := congrArg (fun n : ℕ => n % a) h
  have hdiv := congrArg (fun n : ℕ => n / a) h
  have hi_mod : (a * x + i) % a = i := by
    rw [Nat.add_mod, Nat.mul_mod_right]
    simp [Nat.mod_eq_of_lt hi]
  have hj_mod : (a * y + j) % a = j := by
    rw [Nat.add_mod, Nat.mul_mod_right]
    simp [Nat.mod_eq_of_lt hj]
  have hij : i = j := by simpa [hi_mod, hj_mod] using hmod
  have hi_div : (a * x + i) / a = x := by
    rw [Nat.add_comm]
    rw [Nat.add_mul_div_left _ _ ha]
    rw [Nat.div_eq_of_lt hi]
    simp
  have hj_div : (a * y + j) / a = y := by
    rw [Nat.add_comm]
    rw [Nat.add_mul_div_left _ _ ha]
    rw [Nat.div_eq_of_lt hj]
    simp
  have hxy : x = y := by simpa [hi_div, hj_div] using hdiv
  exact ⟨hxy, hij⟩

lemma le_sub_of_mod_eq_of_lt {a u v : ℕ}
    (h : u % a = v % a) (huv : u < v) : a ≤ v - u := by
  have hmodeq : u ≡ v [MOD a] := h
  have hdvd : a ∣ v - u := by
    exact (Nat.modEq_iff_dvd' huv.le).mp hmodeq
  exact Nat.le_of_dvd (by omega) hdvd

lemma one_le_log_of_three_le {d : ℕ} (hd : 3 ≤ d) : 1 ≤ Real.log (d : ℝ) := by
  have hexp_le : Real.exp 1 ≤ (d : ℝ) := by
    have hlt : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
    exact hlt.le.trans (by exact_mod_cast hd)
  rw [← Real.log_exp 1]
  exact Real.log_le_log (by positivity) hexp_le


/-- Copy adjacency for `a` interleaved copies of `G` inside `Fin m`. -/
def CopyAdj {n₀ : ℕ} (a m : ℕ) (G : SimpleGraph (Fin n₀)) (u v : Fin m) : Prop :=
  ∃ (x y : Fin n₀) (i : ℕ),
    i < a ∧ G.Adj x y ∧ (u : ℕ) = a * (x : ℕ) + i ∧ (v : ℕ) = a * (y : ℕ) + i

lemma copyAdj_symm {n₀ a m : ℕ} {G : SimpleGraph (Fin n₀)} {u v : Fin m}
    (h : CopyAdj a m G u v) : CopyAdj a m G v u := by
  rcases h with ⟨x, y, i, hi, hxy, hu, hv⟩
  exact ⟨y, x, i, hi, G.symm hxy, hv, hu⟩

lemma copyAdj_mod {n₀ a m : ℕ} {G : SimpleGraph (Fin n₀)} {u v : Fin m}
    (h : CopyAdj a m G u v) : (u : ℕ) % a = (v : ℕ) % a := by
  rcases h with ⟨x, y, i, hi, _hxy, hu, hv⟩
  have hu' : (u : ℕ) % a = i := by
    rw [hu, Nat.add_mod, Nat.mul_mod_right]
    simp [Nat.mod_eq_of_lt hi]
  have hv' : (v : ℕ) % a = i := by
    rw [hv, Nat.add_mod, Nat.mul_mod_right]
    simp [Nat.mod_eq_of_lt hi]
  exact hu'.trans hv'.symm

lemma copyAdj_lt {n₀ a m : ℕ} {G : SimpleGraph (Fin n₀)} {u v : Fin m}
    (h : CopyAdj a m G u v) : (u : ℕ) < a * n₀ ∧ (v : ℕ) < a * n₀ := by
  rcases h with ⟨x, y, i, hi, _hxy, hu, hv⟩
  constructor
  · rw [hu]
    calc
      a * (x : ℕ) + i < a * (x : ℕ) + a := Nat.add_lt_add_left hi _
      _ = a * ((x : ℕ) + 1) := by ring
      _ ≤ a * n₀ := Nat.mul_le_mul_left a (Nat.succ_le_of_lt x.isLt)
  · rw [hv]
    calc
      a * (y : ℕ) + i < a * (y : ℕ) + a := Nat.add_lt_add_left hi _
      _ = a * ((y : ℕ) + 1) := by ring
      _ ≤ a * n₀ := Nat.mul_le_mul_left a (Nat.succ_le_of_lt y.isLt)


def PathAdj {m : ℕ} (u v : Fin m) : Prop :=
  (u : ℕ) + 1 = (v : ℕ) ∨ (v : ℕ) + 1 = (u : ℕ)

lemma PathAdj.symm {m : ℕ} {u v : Fin m} (h : PathAdj u v) : PathAdj v u := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

lemma mod_eq_close_two_contra {a p q : ℕ} (ha : 3 ≤ a) (hmod : p % a = q % a)
    (hne : p ≠ q) (hpq : p ≤ q + 2) (hqp : q ≤ p + 2) : False := by
  rcases lt_trichotomy p q with hpq_lt | hpq_eq | hqp_lt
  · have hle : a ≤ q - p := le_sub_of_mod_eq_of_lt hmod hpq_lt
    omega
  · exact hne hpq_eq
  · have hle : a ≤ p - q := le_sub_of_mod_eq_of_lt hmod.symm hqp_lt
    omega

lemma path_close_two {m : ℕ} {u v : Fin m} (h : PathAdj u v) :
    (u : ℕ) ≤ (v : ℕ) + 2 ∧ (v : ℕ) ≤ (u : ℕ) + 2 := by
  rcases h with h | h <;> omega

lemma path_path_close_two {m : ℕ} {u v w : Fin m} (huw : PathAdj u w)
    (hvw : PathAdj v w) :
    (u : ℕ) ≤ (v : ℕ) + 2 ∧ (v : ℕ) ≤ (u : ℕ) + 2 := by
  rcases huw with huw | huw <;> rcases hvw with hvw | hvw <;> omega

lemma path_triangle_contra {m : ℕ} {u v w : Fin m} (hne_uv : u ≠ v) (hne_uw : u ≠ w)
    (hne_vw : v ≠ w) (huv : PathAdj u v) (huw : PathAdj u w) (hvw : PathAdj v w) :
    False := by
  have huv_ne : (u : ℕ) ≠ (v : ℕ) := fun h => hne_uv (Fin.ext h)
  have huw_ne : (u : ℕ) ≠ (w : ℕ) := fun h => hne_uw (Fin.ext h)
  have hvw_ne : (v : ℕ) ≠ (w : ℕ) := fun h => hne_vw (Fin.ext h)
  rcases huv with huv | huv <;> rcases huw with huw | huw <;> rcases hvw with hvw | hvw <;> omega

lemma copy_path_path_contra {n₀ a m : ℕ} {G : SimpleGraph (Fin n₀)} {u v w : Fin m}
    (ha : 3 ≤ a) (hne_uv : u ≠ v) (huv : CopyAdj a m G u v)
    (huw : PathAdj u w) (hvw : PathAdj v w) : False := by
  have hmod : (u : ℕ) % a = (v : ℕ) % a := copyAdj_mod huv
  have hne : (u : ℕ) ≠ (v : ℕ) := fun h => hne_uv (Fin.ext h)
  have hclose := path_path_close_two huw hvw
  exact mod_eq_close_two_contra ha hmod hne hclose.1 hclose.2

lemma copy_copy_path_contra {n₀ a m : ℕ} {G : SimpleGraph (Fin n₀)} {u v w : Fin m}
    (ha : 3 ≤ a) (hne_uv : u ≠ v) (huw : CopyAdj a m G u w)
    (hvw : CopyAdj a m G v w) (huv : PathAdj u v) : False := by
  have hmod_uw : (u : ℕ) % a = (w : ℕ) % a := copyAdj_mod huw
  have hmod_vw : (v : ℕ) % a = (w : ℕ) % a := copyAdj_mod hvw
  have hmod : (u : ℕ) % a = (v : ℕ) % a := hmod_uw.trans hmod_vw.symm
  have hne : (u : ℕ) ≠ (v : ℕ) := fun h => hne_uv (Fin.ext h)
  have hclose := path_close_two huv
  exact mod_eq_close_two_contra ha hmod hne hclose.1 hclose.2

lemma copy_copy_copy_contra {n₀ a m : ℕ} {G : SimpleGraph (Fin n₀)} {u v w : Fin m}
    (hG : G.CliqueFree 3) (huv : CopyAdj a m G u v) (huw : CopyAdj a m G u w)
    (hvw : CopyAdj a m G v w) : False := by
  rcases huv with ⟨xuv, yuv, iuv, hiuv, hxy, hu1, hv1⟩
  rcases huw with ⟨xuw, yuw, iuw, hiuw, hxw, hu2, hw2⟩
  rcases hvw with ⟨xvw, yvw, ivw, hivw, hyv, hv2, hw3⟩
  have hux : xuv = xuw := by
    apply Fin.ext
    exact (decomp_unique hiuv hiuw (hu1.symm.trans hu2)).1
  have hvx : yuv = xvw := by
    apply Fin.ext
    exact (decomp_unique hiuv hivw (hv1.symm.trans hv2)).1
  have hwx : yuw = yvw := by
    apply Fin.ext
    exact (decomp_unique hiuw hivw (hw2.symm.trans hw3)).1
  subst xuw
  subst xvw
  subst yvw
  exact hG {xuv, yuv, yuw} (SimpleGraph.is3Clique_iff.mpr ⟨xuv, yuv, yuw, hxy, hxw, hyv, rfl⟩)

/-- The glued host graph: interleaved copies plus a Hamiltonian path. -/
def glued {n₀ : ℕ} (a m : ℕ) (G : SimpleGraph (Fin n₀)) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun u v => CopyAdj a m G u v ∨ (u : ℕ) + 1 = (v : ℕ)

lemma glued_adj {n₀ : ℕ} (a m : ℕ) (G : SimpleGraph (Fin n₀)) (u v : Fin m) :
    (glued a m G).Adj u v ↔
      u ≠ v ∧
        (CopyAdj a m G u v ∨ (u : ℕ) + 1 = (v : ℕ) ∨ (v : ℕ) + 1 = (u : ℕ)) := by
  simp only [glued, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, (hc | hp) | (hc | hp)⟩
    · exact ⟨hne, Or.inl hc⟩
    · exact ⟨hne, Or.inr (Or.inl hp)⟩
    · exact ⟨hne, Or.inl (copyAdj_symm hc)⟩
    · exact ⟨hne, Or.inr (Or.inr hp)⟩
  · rintro ⟨hne, hc | hp | hp⟩
    · exact ⟨hne, Or.inl (Or.inl hc)⟩
    · exact ⟨hne, Or.inl (Or.inr hp)⟩
    · exact ⟨hne, Or.inr (Or.inr hp)⟩



lemma pathNbr_ncard_le_two {m : ℕ} (v : Fin m) :
    ({u : Fin m | PathAdj v u} : Set (Fin m)).ncard ≤ 2 := by
  classical
  let f : Fin m → Bool := fun u => decide ((u : ℕ) + 1 = (v : ℕ))
  have hle : ({u : Fin m | PathAdj v u} : Set (Fin m)).ncard ≤ (Set.univ : Set Bool).ncard := by
    refine Set.ncard_le_ncard_of_injOn f (by intro u hu; simp) ?_
    intro u hu u' hu' hdec
    rcases hu with hu | hu <;> rcases hu' with hu' | hu'
    · apply Fin.ext
      omega
    · exfalso
      have hnot : ¬ (u : ℕ) + 1 = (v : ℕ) := by omega
      simp [f, hnot, hu'] at hdec
    · exfalso
      have hnot : ¬ (u' : ℕ) + 1 = (v : ℕ) := by omega
      simp [f, hu, hnot] at hdec
    · apply Fin.ext
      omega
  simpa [Nat.card_eq_fintype_card] using hle

lemma copyNbr_ncard_le {n₀ a m : ℕ} {G : SimpleGraph (Fin n₀)} (ha : 0 < a)
    {v : Fin m} (hv : (v : ℕ) < a * n₀) :
    ({u : Fin m | CopyAdj a m G v u} : Set (Fin m)).ncard ≤
      (G.neighborSet ⟨(v : ℕ) / a, by
        have hv' : (v : ℕ) < n₀ * a := by simpa [Nat.mul_comm] using hv
        exact (Nat.div_lt_iff_lt_mul ha).2 hv'⟩).ncard := by
  classical
  have hn₀ : 0 < n₀ := by
    by_contra h
    have hn : n₀ = 0 := Nat.eq_zero_of_not_pos h
    simp [hn] at hv
  let xv : Fin n₀ := ⟨(v : ℕ) / a, by
    have hv' : (v : ℕ) < n₀ * a := by simpa [Nat.mul_comm] using hv
    exact (Nat.div_lt_iff_lt_mul ha).2 hv'⟩
  let f : Fin m → Fin n₀ := fun u =>
    if hu : (u : ℕ) < a * n₀ then
      ⟨(u : ℕ) / a, by
        have hu' : (u : ℕ) < n₀ * a := by simpa [Nat.mul_comm] using hu
        exact (Nat.div_lt_iff_lt_mul ha).2 hu'⟩
    else
      ⟨0, hn₀⟩
  refine Set.ncard_le_ncard_of_injOn f ?_ ?_
  · intro u hu
    have hu_lt : (u : ℕ) < a * n₀ := (copyAdj_lt hu).2
    rcases hu with ⟨x, y, i, hi, hxy, hv_eq, hu_eq⟩
    have hx : x = xv := by
      apply Fin.ext
      exact (decomp_unique hi (Nat.mod_lt _ ha)
        (hv_eq.symm.trans (Nat.div_add_mod (v : ℕ) a).symm)).1
    have hf_eq : f u = y := by
      apply Fin.ext
      have hy : (u : ℕ) / a = (y : ℕ) := by
        rw [hu_eq, Nat.mul_add_div ha, Nat.div_eq_of_lt hi]
        simp
      simp [f, hu_lt, hy]
    change G.Adj xv (f u)
    rw [← hx, hf_eq]
    exact hxy
  · intro u hu u' hu' hEq
    apply Fin.ext
    have hu_lt : (u : ℕ) < a * n₀ := (copyAdj_lt hu).2
    have hu'_lt : (u' : ℕ) < a * n₀ := (copyAdj_lt hu').2
    have hquot : (u : ℕ) / a = (u' : ℕ) / a := by
      have hval := congrArg Fin.val hEq
      simpa [f, hu_lt, hu'_lt] using hval
    have hmod_u : (u : ℕ) % a = (v : ℕ) % a := (copyAdj_mod hu).symm
    have hmod_u' : (u' : ℕ) % a = (v : ℕ) % a := (copyAdj_mod hu').symm
    calc
      (u : ℕ) = a * ((u : ℕ) / a) + (u : ℕ) % a :=
        (Nat.div_add_mod (u : ℕ) a).symm
      _ = a * ((u' : ℕ) / a) + (u' : ℕ) % a := by
        rw [hquot, hmod_u, hmod_u']
      _ = (u' : ℕ) := Nat.div_add_mod (u' : ℕ) a


def copyProj {n₀ a m : ℕ} (hn₀ : 0 < n₀) (ha : 0 < a) (u : Fin m) : Fin n₀ :=
  if hu : (u : ℕ) < a * n₀ then
    ⟨(u : ℕ) / a, by
      have hu' : (u : ℕ) < n₀ * a := by simpa [Nat.mul_comm] using hu
      exact (Nat.div_lt_iff_lt_mul ha).2 hu'⟩
  else
    ⟨0, hn₀⟩

lemma copyProj_val_of_lt {n₀ a m : ℕ} (hn₀ : 0 < n₀) (ha : 0 < a) {u : Fin m}
    (hu : (u : ℕ) < a * n₀) :
    (copyProj (n₀ := n₀) (a := a) (m := m) hn₀ ha u : ℕ) = (u : ℕ) / a := by
  simp [copyProj, hu]

lemma tail_card_le {n₀ a b m : ℕ} (hm_eq : a * n₀ + b = m) (s : Finset (Fin m)) :
    (s.filter (fun w : Fin m => ¬ ((w : ℕ) < a * n₀))).card ≤ b := by
  classical
  let c := a * n₀
  have hm_eq' : c + b = m := by simpa [c] using hm_eq
  have hle : (s.filter (fun w : Fin m => ¬ ((w : ℕ) < a * n₀))).card ≤ (Finset.range b).card := by
    refine Finset.card_le_card_of_injOn (fun w : Fin m => (w : ℕ) - c) ?_ ?_
    · intro w hw
      have hwF : w ∈ s.filter (fun w : Fin m => ¬ ((w : ℕ) < a * n₀)) := by simpa using hw
      rw [Finset.mem_filter] at hwF
      have hcw : c ≤ (w : ℕ) := le_of_not_gt hwF.2
      have hwm : (w : ℕ) < c + b := by
        rw [hm_eq']
        exact w.isLt
      exact Finset.mem_range.mpr (Nat.sub_lt_left_of_lt_add hcw hwm)
    · intro x hx y hy hxy
      have hxF : x ∈ s.filter (fun w : Fin m => ¬ ((w : ℕ) < a * n₀)) := by simpa using hx
      have hyF : y ∈ s.filter (fun w : Fin m => ¬ ((w : ℕ) < a * n₀)) := by simpa using hy
      rw [Finset.mem_filter] at hxF hyF
      apply Fin.ext
      have hcx : c ≤ (x : ℕ) := le_of_not_gt hxF.2
      have hcy : c ≤ (y : ℕ) := le_of_not_gt hyF.2
      have hxy_add := congrArg (fun n : ℕ => n + c) hxy
      simpa [Nat.sub_add_cancel hcx, Nat.sub_add_cancel hcy] using hxy_add
  simpa using hle

lemma head_fiber_card_le_indepNum {n₀ a m r : ℕ} {G : SimpleGraph (Fin n₀)}
    (hn₀ : 0 < n₀) (ha : 0 < a) (hr : r < a) {s : Finset (Fin m)}
    (hs : (glued a m G).IsIndepSet ↑s) :
    ((s.filter (fun w : Fin m => (w : ℕ) < a * n₀)).filter
        (fun w : Fin m => (w : ℕ) % a = r)).card ≤
      G.indepNum := by
  classical
  let head : Finset (Fin m) := s.filter (fun w : Fin m => (w : ℕ) < a * n₀)
  let fiber : Finset (Fin m) := head.filter (fun w : Fin m => (w : ℕ) % a = r)
  let proj : Fin m → Fin n₀ := copyProj hn₀ ha
  have hinj : (fiber : Set (Fin m)).InjOn proj := by
    intro x hx y hy hxy
    have hxF : x ∈ fiber := by simpa using hx
    have hyF : y ∈ fiber := by simpa using hy
    rw [Finset.mem_filter] at hxF hyF
    have hxH : x ∈ head := hxF.1
    have hyH : y ∈ head := hyF.1
    rw [Finset.mem_filter] at hxH hyH
    have hxlt : (x : ℕ) < a * n₀ := hxH.2
    have hylt : (y : ℕ) < a * n₀ := hyH.2
    have hxmod : (x : ℕ) % a = r := hxF.2
    have hymod : (y : ℕ) % a = r := hyF.2
    have hquot : (x : ℕ) / a = (y : ℕ) / a := by
      have hval := congrArg Fin.val hxy
      simpa [proj, copyProj_val_of_lt hn₀ ha hxlt, copyProj_val_of_lt hn₀ ha hylt] using hval
    apply Fin.ext
    calc
      (x : ℕ) = a * ((x : ℕ) / a) + (x : ℕ) % a := (Nat.div_add_mod (x : ℕ) a).symm
      _ = a * ((y : ℕ) / a) + (y : ℕ) % a := by rw [hquot, hxmod, hymod]
      _ = (y : ℕ) := Nat.div_add_mod (y : ℕ) a
  let image : Finset (Fin n₀) := fiber.image proj
  have hcard_image : image.card = fiber.card := by
    simpa [image] using Finset.card_image_of_injOn hinj
  have hind : G.IsIndepSet (image : Set (Fin n₀)) := by
    rintro x hx y hy hne hxy
    have hxI : x ∈ image := by simpa using hx
    have hyI : y ∈ image := by simpa using hy
    rw [Finset.mem_image] at hxI hyI
    rcases hxI with ⟨wx, hwx, rfl⟩
    rcases hyI with ⟨wy, hwy, rfl⟩
    rw [Finset.mem_filter] at hwx hwy
    have hwxH : wx ∈ head := hwx.1
    have hwyH : wy ∈ head := hwy.1
    rw [Finset.mem_filter] at hwxH hwyH
    have hwx_s : wx ∈ s := hwxH.1
    have hwy_s : wy ∈ s := hwyH.1
    have hwx_lt : (wx : ℕ) < a * n₀ := hwxH.2
    have hwy_lt : (wy : ℕ) < a * n₀ := hwyH.2
    have hwx_mod : (wx : ℕ) % a = r := hwx.2
    have hwy_mod : (wy : ℕ) % a = r := hwy.2
    have hne_w : wx ≠ wy := by
      intro h
      exact hne (by rw [h])
    have hwx_val : (wx : ℕ) = a * ((proj wx : Fin n₀) : ℕ) + r := by
      have hp := copyProj_val_of_lt hn₀ ha hwx_lt
      calc
        (wx : ℕ) = a * ((wx : ℕ) / a) + (wx : ℕ) % a := (Nat.div_add_mod (wx : ℕ) a).symm
        _ = a * ((proj wx : Fin n₀) : ℕ) + r := by rw [hp, hwx_mod]
    have hwy_val : (wy : ℕ) = a * ((proj wy : Fin n₀) : ℕ) + r := by
      have hp := copyProj_val_of_lt hn₀ ha hwy_lt
      calc
        (wy : ℕ) = a * ((wy : ℕ) / a) + (wy : ℕ) % a := (Nat.div_add_mod (wy : ℕ) a).symm
        _ = a * ((proj wy : Fin n₀) : ℕ) + r := by rw [hp, hwy_mod]
    have hcopy : CopyAdj a m G wx wy := by
      exact ⟨proj wx, proj wy, r, hr, hxy, hwx_val, hwy_val⟩
    have hglued : (glued a m G).Adj wx wy := by
      rw [glued_adj]
      exact ⟨hne_w, Or.inl hcopy⟩
    exact hs hwx_s hwy_s hne_w hglued
  have hle := hind.card_le_indepNum (t := image)
  rw [hcard_image] at hle
  simpa [head, fiber] using hle

lemma glued_indep_card {n₀ a b m : ℕ} {G : SimpleGraph (Fin n₀)}
    (hn₀ : 0 < n₀) (ha : 0 < a) (hm_eq : a * n₀ + b = m)
    {s : Finset (Fin m)} (hs : (glued a m G).IsIndepSet ↑s) :
    s.card ≤ a * G.indepNum + b := by
  classical
  let head : Finset (Fin m) := s.filter (fun w : Fin m => (w : ℕ) < a * n₀)
  let tail : Finset (Fin m) := s.filter (fun w : Fin m => ¬ ((w : ℕ) < a * n₀))
  have hsplit : head.card + tail.card = s.card := by
    simpa [head, tail] using Finset.card_filter_add_card_filter_not (s := s)
      (p := fun w : Fin m => (w : ℕ) < a * n₀)
  have htail : tail.card ≤ b := by
    simpa [tail] using tail_card_le (n₀ := n₀) (a := a) (b := b) hm_eq s
  have hhead_eq :
      head.card = ∑ r ∈ Finset.range a,
        (head.filter (fun w : Fin m => (w : ℕ) % a = r)).card := by
    exact Finset.card_eq_sum_card_fiberwise (s := head) (t := Finset.range a)
      (f := fun w : Fin m => (w : ℕ) % a) (by
        intro w hw
        exact Finset.mem_range.mpr (Nat.mod_lt _ ha))
  have hhead_le : head.card ≤ a * G.indepNum := by
    rw [hhead_eq]
    calc
      (∑ r ∈ Finset.range a, (head.filter (fun w : Fin m => (w : ℕ) % a = r)).card)
          ≤ ∑ r ∈ Finset.range a, G.indepNum := by
        refine Finset.sum_le_sum ?_
        intro r hr
        exact head_fiber_card_le_indepNum (G := G) hn₀ ha (Finset.mem_range.1 hr) hs
      _ = a * G.indepNum := by
        simp [Finset.sum_const]
  omega

lemma glued_indepNum {n₀ a b m : ℕ} {G : SimpleGraph (Fin n₀)}
    (hn₀ : 0 < n₀) (ha : 0 < a) (hm_eq : a * n₀ + b = m) :
    (glued a m G).indepNum ≤ a * G.indepNum + b := by
  classical
  rcases (glued a m G).exists_isNIndepSet_indepNum with ⟨s, hs⟩
  have hle := glued_indep_card (G := G) hn₀ ha hm_eq hs.isIndepSet
  simpa [hs.card_eq] using hle


lemma host_budget {d n₀ a b m αG : ℕ} (hd3 : 3 ≤ d)
    (hm_eq : a * n₀ + b = m) (hb : b ≤ n₀) (hmd : n₀ * d ≤ m)
    (hα : (αG : ℝ) ≤ 14 * (n₀ : ℝ) * Real.log (d : ℝ) / (d : ℝ)) :
    ((a * αG + b : ℕ) : ℝ) ≤ 15 * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) := by
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hd3)
  have hlog1 : 1 ≤ Real.log (d : ℝ) := one_le_log_of_three_le hd3
  have hlog_nonneg : 0 ≤ Real.log (d : ℝ) := by linarith
  have han_nat : a * n₀ ≤ m := by
    rw [← hm_eq]
    exact Nat.le_add_right (a * n₀) b
  have han : (a : ℝ) * (n₀ : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast han_nat
  have hbmd_nat : b * d ≤ m := by
    exact (Nat.mul_le_mul_right d hb).trans hmd
  have hb_div : (b : ℝ) ≤ (m : ℝ) / (d : ℝ) := by
    have hbmul : (b : ℝ) * (d : ℝ) ≤ (m : ℝ) := by exact_mod_cast hbmd_nat
    rw [le_div_iff₀ hdpos]
    simpa [mul_comm] using hbmul
  have hb_part : (b : ℝ) ≤ (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) := by
    calc
      (b : ℝ) ≤ (m : ℝ) / (d : ℝ) := hb_div
      _ = (m : ℝ) * 1 / (d : ℝ) := by ring
      _ ≤ (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) := by
        refine div_le_div_of_nonneg_right ?_ hdpos.le
        exact mul_le_mul_of_nonneg_left hlog1 (by positivity)
  have hα_part : (((a * αG : ℕ) : ℝ)) ≤
      14 * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) := by
    calc
      (((a * αG : ℕ) : ℝ)) = (a : ℝ) * (αG : ℝ) := by norm_num
      _ ≤ (a : ℝ) * (14 * (n₀ : ℝ) * Real.log (d : ℝ) / (d : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hα (by positivity)
      _ = 14 * ((a : ℝ) * (n₀ : ℝ)) * Real.log (d : ℝ) / (d : ℝ) := by ring
      _ ≤ 14 * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) := by
        have hpre : 14 * ((a : ℝ) * (n₀ : ℝ)) * Real.log (d : ℝ) ≤
            14 * (m : ℝ) * Real.log (d : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left han (by norm_num : (0 : ℝ) ≤ 14)) hlog_nonneg
        exact div_le_div_of_nonneg_right hpre hdpos.le
  calc
    ((a * αG + b : ℕ) : ℝ) = (((a * αG : ℕ) : ℝ)) + (b : ℝ) := by norm_num
    _ ≤ 14 * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) +
        (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) := add_le_add hα_part hb_part
    _ = 15 * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) := by ring

lemma glued_degree {n₀ a m d : ℕ} (G : SimpleGraph (Fin n₀)) (hd3 : 3 ≤ d) (ha : 0 < a)
    (hdeg : ∀ x : Fin n₀, (G.neighborSet x).ncard + 3 ≤ d) :
    ∀ v : Fin m, ((glued a m G).neighborSet v).ncard ≤ d := by
  intro v
  let Cnbr : Set (Fin m) := {u | CopyAdj a m G v u}
  let Pnbr : Set (Fin m) := {u | PathAdj v u}
  have hsub : (glued a m G).neighborSet v ⊆ Cnbr ∪ Pnbr := by
    intro u hu
    have h := (glued_adj a m G v u).1 hu
    rcases h with ⟨_hne, hc | hp⟩
    · exact Set.mem_union_left Pnbr hc
    · exact Set.mem_union_right Cnbr hp
  have hsplit : ((glued a m G).neighborSet v).ncard ≤ Cnbr.ncard + Pnbr.ncard := by
    exact (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le Cnbr Pnbr)
  have hpath : Pnbr.ncard ≤ 2 := by
    simpa [Pnbr] using pathNbr_ncard_le_two v
  by_cases hv : (v : ℕ) < a * n₀
  · let xv : Fin n₀ := ⟨(v : ℕ) / a, by
      have hv' : (v : ℕ) < n₀ * a := by simpa [Nat.mul_comm] using hv
      exact (Nat.div_lt_iff_lt_mul ha).2 hv'⟩
    have hcopy : Cnbr.ncard ≤ (G.neighborSet xv).ncard := by
      simpa [Cnbr, xv] using copyNbr_ncard_le (G := G) ha (v := v) hv
    have hseed := hdeg xv
    omega
  · have hcopy0 : Cnbr.ncard = 0 := by
      have hEmpty : Cnbr = ∅ := by
        ext u
        constructor
        · intro hu
          exact False.elim (hv (copyAdj_lt hu).1)
        · intro hu
          simp at hu
      simp [hEmpty]
    omega

lemma glued_cliqueFree {n₀ a m : ℕ} (G : SimpleGraph (Fin n₀)) (ha : 3 ≤ a)
    (hG : G.CliqueFree 3) : (glued a m G).CliqueFree 3 := by
  intro s hs
  rw [SimpleGraph.is3Clique_iff] at hs
  rcases hs with ⟨u, v, w, huv, huw, hvw, rfl⟩
  have huv' := (glued_adj a m G u v).1 huv
  have huw' := (glued_adj a m G u w).1 huw
  have hvw' := (glued_adj a m G v w).1 hvw
  rcases huv' with ⟨hne_uv, euv⟩
  rcases huw' with ⟨hne_uw, euw⟩
  rcases hvw' with ⟨hne_vw, evw⟩
  rcases euv with cuv | puv <;> rcases euw with cuw | puw <;> rcases evw with cvw | pvw
  · exact copy_copy_copy_contra hG cuv cuw cvw
  · exact copy_copy_path_contra ha hne_vw (copyAdj_symm cuv) (copyAdj_symm cuw) pvw
  · exact copy_copy_path_contra ha hne_uw cuv (copyAdj_symm cvw) puw
  · exact copy_path_path_contra ha hne_uv cuv puw pvw
  · exact copy_copy_path_contra ha hne_uv cuw cvw puv
  · exact copy_path_path_contra ha hne_uw cuw puv (PathAdj.symm pvw)
  · exact copy_path_path_contra ha hne_vw cvw (PathAdj.symm puv) (PathAdj.symm puw)
  · exact path_triangle_contra hne_uv hne_uw hne_vw puv puw pvw

lemma reachable_zero {n₀ a m : ℕ} (G : SimpleGraph (Fin n₀)) (hm : 0 < m) :
    ∀ k (hk : k < m), (glued a m G).Reachable ⟨0, hm⟩ ⟨k, hk⟩ := by
  intro k
  induction k with
  | zero =>
      intro hk
      exact Reachable.refl _
  | succ k ih =>
      intro hk
      have hk' : k < m := by omega
      have hadj : (glued a m G).Adj ⟨k, hk'⟩ ⟨k + 1, hk⟩ := by
        rw [glued_adj]
        refine ⟨?_, Or.inr (Or.inl rfl)⟩
        exact Fin.ne_of_val_ne (by simp)
      exact (ih hk').trans hadj.reachable

lemma glued_connected {n₀ a m : ℕ} (G : SimpleGraph (Fin n₀)) (hm : 0 < m) :
    (glued a m G).Connected := by
  refine { preconnected := ?_, nonempty := ⟨⟨0, hm⟩⟩ }
  intro x y
  have hx : (glued a m G).Reachable ⟨0, hm⟩ x := by
    simpa [Fin.eta] using reachable_zero (a := a) G hm x.val x.isLt
  have hy : (glued a m G).Reachable ⟨0, hm⟩ y := by
    simpa [Fin.eta] using reachable_zero (a := a) G hm y.val y.isLt
  exact hx.symm.trans hy

end Gluing

/-- Deterministic gluing step from the seed graph to the host graph.

For large `m`, take `a = m / n₀` interleaved copies of the seed graph in `Fin m`, leave the
`m % n₀` remaining vertices outside the copied region, and add the Hamiltonian path on `Fin m`.
The interleaving separates copy edges by residue modulo `a`, so for `a ≥ 3` the path creates no
triangles with the copied seed graph. -/
theorem seed_graph_to_host :
    ∀ᶠ d : ℕ in Filter.atTop,
      ∀ (n₀ : ℕ) (G : SimpleGraph (Fin n₀)),
        0 < n₀ →
          SeedGraph d n₀ G →
            ∀ᶠ m : ℕ in Filter.atTop,
              ∃ H : SimpleGraph (Fin m), HostGraph d m H := by
  refine Filter.Eventually.of_forall ?_
  intro d n₀ G hn₀ hG
  have hd3 : 3 ≤ d := by
    have hdeg0 := hG.2.1 ⟨0, hn₀⟩
    omega
  filter_upwards [Filter.eventually_ge_atTop (3 * n₀),
      Filter.eventually_ge_atTop (n₀ * d),
      Filter.eventually_ge_atTop 1] with m hm3 hmd hm1
  set a := m / n₀ with ha_def
  set b := m % n₀ with hb_def
  have ha3 : 3 ≤ a := by
    rw [ha_def]
    exact (Nat.le_div_iff_mul_le hn₀).2 hm3
  have ha0 : 0 < a := by omega
  have hm_eq : a * n₀ + b = m := by
    rw [ha_def, hb_def, mul_comm]
    exact Nat.div_add_mod m n₀
  have hb_lt : b < n₀ := by
    rw [hb_def]
    exact Nat.mod_lt m hn₀
  refine ⟨Gluing.glued a m G, ?_, ?_, ?_, ?_⟩
  · exact Gluing.glued_connected (a := a) G (by omega)
  · exact Gluing.glued_cliqueFree (a := a) G ha3 hG.1
  · exact Gluing.glued_degree (a := a) (d := d) G hd3 ha0 hG.2.1
  · calc
      ((Gluing.glued a m G).indepNum : ℝ)
          ≤ ((a * G.indepNum + b : ℕ) : ℝ) := by
            exact_mod_cast Gluing.glued_indepNum (G := G) hn₀ ha0 hm_eq
      _ ≤ 15 * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) :=
            Gluing.host_budget hd3 hm_eq hb_lt.le hmd hG.2.2

/-- Lemma E, with the original statement copied from `Solution.lean`. -/
theorem lemmaE_host_graphs :
    ∀ᶠ d : ℕ in Filter.atTop,
      ∀ᶠ m : ℕ in Filter.atTop,
        ∃ H : SimpleGraph (Fin m), HostGraph d m H := by
  filter_upwards [seed_graph_exists, seed_graph_to_host] with d hSeed hGlue
  rcases hSeed with ⟨n₀, hn₀, G, hG⟩
  exact hGlue n₀ G hn₀ hG

/-- A feasible `h_r` supergraph for the challenge definition. -/
def FeasibleSupergraph {n : ℕ} (r : ℕ) (G H : SimpleGraph (Fin n)) : Prop :=
  G ≤ H ∧ H.CliqueFree 3 ∧ H.ediam ≤ (r : ℕ∞)

/-- On a finite vertex type, any nonempty feasible set has a least added-edge count, hence an
`IsHR` witness. -/
theorem exists_isHR_of_exists_feasible {n r : ℕ} {G : SimpleGraph (Fin n)}
    (hfeas : ∃ H : SimpleGraph (Fin n), FeasibleSupergraph r G H) :
    ∃ m : ℕ, IsHR r G m := by
  classical
  let P : ℕ → Prop := fun m =>
    ∃ H : SimpleGraph (Fin n),
      FeasibleSupergraph r G H ∧ addedEdgeCount G H = m
  have hP : ∃ m, P m := by
    rcases hfeas with ⟨H, hH⟩
    exact ⟨addedEdgeCount G H, H, hH, rfl⟩
  let m := Nat.find hP
  have hm : P m := Nat.find_spec hP
  rcases hm with ⟨H, hH, hcount⟩
  refine ⟨m, H, hH.1, hH.2.1, hH.2.2, hcount, ?_⟩
  intro K hGK hKtf hKdiam
  exact Nat.find_min' hP ⟨K, ⟨hGK, hKtf, hKdiam⟩, rfl⟩

/-- If every feasible supergraph has at least `L` new edges, then the `h_r` value has at least
`L` new edges. -/
theorem exists_isHR_with_real_lower_bound {n r : ℕ} {G : SimpleGraph (Fin n)} {L : ℝ}
    (hfeas : ∃ H : SimpleGraph (Fin n), FeasibleSupergraph r G H)
    (hlower : ∀ H : SimpleGraph (Fin n), FeasibleSupergraph r G H →
      L ≤ (addedEdgeCount G H : ℝ)) :
    ∃ m : ℕ, IsHR r G m ∧ L ≤ (m : ℝ) := by
  rcases exists_isHR_of_exists_feasible (r := r) (G := G) hfeas with ⟨m, hm⟩
  rcases hm with ⟨H, hGH, hHtf, hHdiam, hcount, hmin⟩
  refine ⟨m, ⟨H, hGH, hHtf, hHdiam, hcount, hmin⟩, ?_⟩
  simpa [hcount] using hlower H ⟨hGH, hHtf, hHdiam⟩


/-- It is enough to bound explicit walks between all ordered pairs to bound extended diameter. -/
lemma ediam_le_of_forall_exists_walk_le {V : Type} (G : SimpleGraph V) {r : ℕ}
    (h : ∀ u v : V, ∃ p : G.Walk u v, p.length ≤ r) : G.ediam ≤ (r : ℕ∞) := by
  rw [SimpleGraph.ediam_le_iff]
  intro u v
  rcases h u v with ⟨p, hp⟩
  exact (SimpleGraph.edist_le p).trans (by exact_mod_cast hp)

/-- Extract a concrete bounded walk from a finite extended-distance bound. -/
lemma exists_walk_length_le_of_edist_le {V : Type} {G : SimpleGraph V} {u v : V} {r : ℕ}
    (h : G.edist u v ≤ (r : ℕ∞)) :
    ∃ p : G.Walk u v, p.length ≤ r := by
  have hne : G.edist u v ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top r) h
  rcases SimpleGraph.exists_walk_of_edist_ne_top hne with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  have hp_le : (p.length : ℕ∞) ≤ (r : ℕ∞) := by
    rw [hp]
    exact h
  exact ENat.coe_le_coe.mp hp_le

/-- Transporting a supergraph relation across the canonical `Fin` copy preserves inclusion. -/
lemma overFin_mono {V : Type} [Fintype V] {n : ℕ} {G K : SimpleGraph V}
    (hc : Fintype.card V = n) (hGK : G ≤ K) :
    G.overFin hc ≤ K.overFin hc := by
  intro x y hxy
  exact hGK hxy

/-- A walk-by-walk diameter bound survives transport to the canonical `Fin` copy. -/
lemma overFin_ediam_le_of_forall_exists_walk_le {V : Type} [Fintype V] {n r : ℕ}
    (G : SimpleGraph V) (hc : Fintype.card V = n)
    (h : ∀ u v : V, ∃ p : G.Walk u v, p.length ≤ r) :
    (G.overFin hc).ediam ≤ (r : ℕ∞) := by
  apply ediam_le_of_forall_exists_walk_le
  intro x y
  let e := SimpleGraph.overFinIso (G := G) hc
  rcases h (e.symm x) (e.symm y) with ⟨p, hp⟩
  have hx : e (e.symm x) = x := by simp
  have hy : e (e.symm y) = y := by simp
  rw [← hx, ← hy]
  exact ⟨p.map e.toHom, by simpa [Walk.length_map] using hp⟩

/-- Distinct connected components have disjoint supports, in pointwise form. -/
lemma connectedComponent_not_mem_supp_of_ne {V : Type} {G : SimpleGraph V}
    {X Y : G.ConnectedComponent} (hXY : X ≠ Y) {v : V} (hv : v ∈ X.supp) :
    v ∉ Y.supp := by
  intro hvY
  exact hXY (SimpleGraph.ConnectedComponent.eq_of_common_vertex hv hvY)

/-- Component-local form of the standard connected graph edge lower bound. -/
lemma connectedComponent_supp_ncard_le_edgeSet_add_one {V : Type} (G : SimpleGraph V)
    (C : G.ConnectedComponent) :
    C.supp.ncard ≤ Nat.card C.toSimpleGraph.edgeSet + 1 := by
  have h := C.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
  simpa [Nat.card_coe_set_eq] using h

lemma connectedComponent_edgeSigma_card_le_edgeSet {V : Type} [Fintype V]
    (G : SimpleGraph V) :
    Nat.card (Σ C : G.ConnectedComponent, C.toSimpleGraph.edgeSet) ≤ Nat.card G.edgeSet := by
  classical
  let edgeMap : (Σ C : G.ConnectedComponent, C.toSimpleGraph.edgeSet) → G.edgeSet := fun z =>
    match z with
    | ⟨C, e⟩ =>
        ⟨Sym2.map Subtype.val e.1, by
          refine Sym2.ind ?_ e.1 e.2
          intro u v huv
          have hG : G.Adj u.1 v.1 := by
            simpa [SimpleGraph.mem_edgeSet, SimpleGraph.ConnectedComponent.toSimpleGraph] using huv
          simpa [SimpleGraph.mem_edgeSet, Sym2.map_pair_eq] using hG⟩
  have hinj : Function.Injective edgeMap := by
    rintro ⟨X, e⟩ ⟨Y, f⟩ h
    have hval : Sym2.map Subtype.val e.1 = Sym2.map Subtype.val f.1 := by
      simpa [edgeMap] using congrArg Subtype.val h
    refine Sym2.ind ?_ e.1 e.2 f.2 hval
    intro u v huv hf hmap
    refine Sym2.ind ?_ f.1 hf hmap
    intro u' v' huv' hmap'
    have hpair : s((u : V), (v : V)) = s((u' : V), (v' : V)) := by
      simpa [Sym2.map_pair_eq] using hmap'
    have hXY : X = Y := by
      rw [Sym2.eq_iff] at hpair
      rcases hpair with ⟨huu, _⟩ | ⟨huv', _⟩
      · have huY : (u : V) ∈ Y := by
          rw [huu]
          exact u'.2
        exact SimpleGraph.ConnectedComponent.eq_of_common_vertex u.2 huY
      · have huY : (u : V) ∈ Y := by
          rw [huv']
          exact v'.2
        exact SimpleGraph.ConnectedComponent.eq_of_common_vertex u.2 huY
    subst Y
    have hef : e = f := by
      apply Subtype.ext
      exact Sym2.map.injective Subtype.val_injective hval
    cases hef
    rfl
  exact Nat.card_le_card_of_injective edgeMap hinj

lemma card_vertex_le_edgeSet_add_connectedComponents {V : Type} [Fintype V]
    (G : SimpleGraph V) :
    Nat.card V ≤ Nat.card G.edgeSet + Nat.card G.ConnectedComponent := by
  classical
  have hverts : Nat.card V = ∑ C : G.ConnectedComponent, C.supp.ncard := by
    rw [Nat.card_eq_fintype_card]
    simp only [← (set_fintype_card_eq_univ_iff _).mpr G.iUnion_connectedComponentSupp,
      ← Set.toFinset_card, Set.toFinset_iUnion SimpleGraph.ConnectedComponent.supp]
    rw [Finset.card_biUnion
      (fun x _ y _ hxy => Set.disjoint_toFinset.mpr
        (SimpleGraph.pairwise_disjoint_supp_connectedComponent _ hxy))]
    simp [Set.ncard_eq_toFinset_card']
  rw [hverts]
  calc
    (∑ C : G.ConnectedComponent, C.supp.ncard) ≤
        ∑ C : G.ConnectedComponent, (Nat.card C.toSimpleGraph.edgeSet + 1) := by
      exact Finset.sum_le_sum fun C _ => connectedComponent_supp_ncard_le_edgeSet_add_one G C
    _ = (∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet) +
        Nat.card G.ConnectedComponent := by
      simp [Finset.sum_add_distrib, Nat.card_eq_fintype_card]
    _ ≤ Nat.card G.edgeSet + Nat.card G.ConnectedComponent := by
      have hEdgeSum : (∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet) ≤
          Nat.card G.edgeSet := by
        have h := connectedComponent_edgeSigma_card_le_edgeSet G
        have hsigma : Nat.card (Σ C : G.ConnectedComponent, C.toSimpleGraph.edgeSet) =
            ∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet := by
          rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
          simp [Nat.card_eq_fintype_card]
        exact le_of_eq_of_le hsigma.symm h
      exact Nat.add_le_add_right hEdgeSum _

/-- A core graph with a family of pendant vertices attached by `root`.  This sum-type version keeps
all graph-theoretic arguments independent of the later `Fin n` encoding arithmetic. -/
def PendantCoreGraphSum {C P : Type} (H : SimpleGraph C) (root : P → C) :
    SimpleGraph (C ⊕ P) where
  Adj x y :=
    match x, y with
    | Sum.inl a, Sum.inl b => H.Adj a b
    | Sum.inl a, Sum.inr p => root p = a
    | Sum.inr p, Sum.inl a => root p = a
    | Sum.inr _, Sum.inr _ => False
  symm := by
    rintro (a | p) (b | q) h
    · exact h.symm
    · simpa using h
    · simpa using h
    · exact False.elim h
  loopless := by
    intro x
    cases x with
    | inl a => exact H.irrefl
    | inr p => exact id

@[simp] lemma pendantCoreGraphSum_adj_core_core {C P : Type} {H : SimpleGraph C} {root : P → C}
    {a b : C} :
    (PendantCoreGraphSum H root).Adj (Sum.inl a) (Sum.inl b) ↔ H.Adj a b := Iff.rfl

@[simp] lemma pendantCoreGraphSum_adj_core_pendant {C P : Type} {H : SimpleGraph C} {root : P → C}
    {a : C} {p : P} :
    (PendantCoreGraphSum H root).Adj (Sum.inl a) (Sum.inr p) ↔ root p = a := Iff.rfl

@[simp] lemma pendantCoreGraphSum_adj_pendant_core {C P : Type} {H : SimpleGraph C} {root : P → C}
    {p : P} {a : C} :
    (PendantCoreGraphSum H root).Adj (Sum.inr p) (Sum.inl a) ↔ root p = a := Iff.rfl

@[simp] lemma pendantCoreGraphSum_not_adj_pendant_pendant {C P : Type} {H : SimpleGraph C}
    {root : P → C} {p q : P} :
    ¬ (PendantCoreGraphSum H root).Adj (Sum.inr p) (Sum.inr q) := by
  simp [PendantCoreGraphSum]



@[simp] lemma pendantCoreGraphSum_adj_pendant_iff {C P : Type} {H : SimpleGraph C} {root : P → C}
    {p : P} {x : C ⊕ P} :
    (PendantCoreGraphSum H root).Adj (Sum.inr p) x ↔ x = Sum.inl (root p) := by
  cases x with
  | inl a =>
      change root p = a ↔ Sum.inl a = Sum.inl (root p)
      simp [eq_comm]
  | inr q => simp

@[simp] lemma pendantCoreGraphSum_adj_iff_pendant {C P : Type} {H : SimpleGraph C} {root : P → C}
    {x : C ⊕ P} {p : P} :
    (PendantCoreGraphSum H root).Adj x (Sum.inr p) ↔ x = Sum.inl (root p) := by
  rw [adj_comm, pendantCoreGraphSum_adj_pendant_iff]


/-- The graph on pendants whose edges are the pendant-pendant edges of a supergraph.  Since the
base pendant-core graph has no pendant-pendant edges, these are exactly the new edges of this
type in any supergraph of the base graph. -/
def PendantPairGraph {C P : Type} (K : SimpleGraph (C ⊕ P)) : SimpleGraph P where
  Adj p q := K.Adj (Sum.inr p) (Sum.inr q)
  symm := by
    intro p q h
    exact h.symm
  loopless := by
    intro p
    exact K.irrefl

@[simp] lemma pendantPairGraph_adj {C P : Type} {K : SimpleGraph (C ⊕ P)} {p q : P} :
    (PendantPairGraph K).Adj p q ↔ K.Adj (Sum.inr p) (Sum.inr q) := Iff.rfl

/-- The core vertices adjacent to a given vertex in a graph on `C ⊕ P`. -/
def CoreNeighborFinset {C P : Type} [Fintype C] (K : SimpleGraph (C ⊕ P))
    (w : C ⊕ P) : Finset C := by
  classical
  exact Finset.univ.filter fun c : C => K.Adj w (Sum.inl c)

@[simp] lemma mem_coreNeighborFinset {C P : Type} [Fintype C]
    {K : SimpleGraph (C ⊕ P)} {w : C ⊕ P} {c : C} :
    c ∈ CoreNeighborFinset K w ↔ K.Adj w (Sum.inl c) := by
  classical
  simp [CoreNeighborFinset]

lemma coreNeighborFinset_isIndepSet_of_triangleFree {C P : Type} [Fintype C]
    {H : SimpleGraph C} {K : SimpleGraph (C ⊕ P)}
    (hKtf : K.CliqueFree 3)
    (hcore : ∀ a b : C, H.Adj a b → K.Adj (Sum.inl a) (Sum.inl b))
    (w : C ⊕ P) : H.IsIndepSet (CoreNeighborFinset K w : Set C) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro a ha b hb hab_ne hab
  have hKind := K.isIndepSet_neighborSet_of_triangleFree hKtf w
  have hwa : Sum.inl a ∈ K.neighborSet w := by simpa using ha
  have hwb : Sum.inl b ∈ K.neighborSet w := by simpa using hb
  exact hKind hwa hwb (by simpa using hab_ne) (hcore a b hab)

lemma coreNeighborFinset_card_le_indepNum_of_triangleFree {C P : Type} [Fintype C]
    {H : SimpleGraph C} {K : SimpleGraph (C ⊕ P)}
    (hKtf : K.CliqueFree 3)
    (hcore : ∀ a b : C, H.Adj a b → K.Adj (Sum.inl a) (Sum.inl b))
    (w : C ⊕ P) :
    (CoreNeighborFinset K w).card ≤ H.indepNum := by
  exact SimpleGraph.IsIndepSet.card_le_indepNum
    (coreNeighborFinset_isIndepSet_of_triangleFree (H := H) hKtf hcore w)

lemma coreNeighborFinset_card_le_indepNum_of_pendantCore_le {C P : Type} [Fintype C]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)}
    (hGK : PendantCoreGraphSum H root ≤ K) (hKtf : K.CliqueFree 3) (w : C ⊕ P) :
    (CoreNeighborFinset K w).card ≤ H.indepNum := by
  apply coreNeighborFinset_card_le_indepNum_of_triangleFree (H := H) hKtf
  intro a b hab
  exact hGK (by simpa using hab)

/-- A component of the pendant-pair graph is core-free if its pendants have no new edge to the
core. Equivalently, every core neighbor in the supergraph is still the original root. -/
def PendantComponentCoreFree {C P : Type} (K : SimpleGraph (C ⊕ P)) (root : P → C)
    (X : (PendantPairGraph K).ConnectedComponent) : Prop :=
  ∀ p : P, p ∈ X.supp → ∀ c : C, K.Adj (Sum.inr p) (Sum.inl c) → c = root p

/-- A component is core-touching if it is not core-free. -/
def PendantComponentCoreTouching {C P : Type} (K : SimpleGraph (C ⊕ P)) (root : P → C)
    (X : (PendantPairGraph K).ConnectedComponent) : Prop :=
  ¬ PendantComponentCoreFree K root X

lemma not_coreFree_iff_exists_new_core_edge {C P : Type} {K : SimpleGraph (C ⊕ P)}
    {root : P → C} {X : (PendantPairGraph K).ConnectedComponent} :
    ¬ PendantComponentCoreFree K root X ↔
      ∃ p : P, p ∈ X.supp ∧ ∃ c : C, K.Adj (Sum.inr p) (Sum.inl c) ∧ c ≠ root p := by
  simp [PendantComponentCoreFree]

lemma coreFree_edge_from_pendant {C P : Type} {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X : (PendantPairGraph K).ConnectedComponent}
    (hfree : PendantComponentCoreFree K root X) {p : P} (hp : p ∈ X.supp)
    {x : C ⊕ P} (hpx : K.Adj (Sum.inr p) x) :
    x = Sum.inl (root p) ∨ ∃ q : P, q ∈ X.supp ∧ x = Sum.inr q := by
  cases x with
  | inl c =>
      left
      exact congrArg Sum.inl (hfree p hp c hpx)
  | inr q =>
      right
      refine ⟨q, ?_, rfl⟩
      exact X.mem_supp_of_adj_mem_supp hp hpx

lemma coreFree_edge_to_pendant {C P : Type} {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X : (PendantPairGraph K).ConnectedComponent}
    (hfree : PendantComponentCoreFree K root X) {p : P} (hp : p ∈ X.supp)
    {x : C ⊕ P} (hxp : K.Adj x (Sum.inr p)) :
    x = Sum.inl (root p) ∨ ∃ q : P, q ∈ X.supp ∧ x = Sum.inr q := by
  simpa [eq_comm] using coreFree_edge_from_pendant (K := K) (root := root) hfree hp hxp.symm

lemma coreFree_edge_from_pendant_eq_root_of_not_in_component {C P : Type}
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X : (PendantPairGraph K).ConnectedComponent}
    (hfree : PendantComponentCoreFree K root X) {p : P} (hp : p ∈ X.supp)
    {x : C ⊕ P} (hpx : K.Adj (Sum.inr p) x)
    (hx : ¬ ∃ q : P, q ∈ X.supp ∧ x = Sum.inr q) :
    x = Sum.inl (root p) := by
  rcases coreFree_edge_from_pendant (K := K) (root := root) hfree hp hpx with hroot | hpend
  · exact hroot
  · exact False.elim (hx hpend)

lemma coreFree_edge_to_pendant_eq_root_of_not_in_component {C P : Type}
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X : (PendantPairGraph K).ConnectedComponent}
    (hfree : PendantComponentCoreFree K root X) {p : P} (hp : p ∈ X.supp)
    {x : C ⊕ P} (hxp : K.Adj x (Sum.inr p))
    (hx : ¬ ∃ q : P, q ∈ X.supp ∧ x = Sum.inr q) :
    x = Sum.inl (root p) := by
  rcases coreFree_edge_to_pendant (K := K) (root := root) hfree hp hxp with hroot | hpend
  · exact hroot
  · exact False.elim (hx hpend)

lemma pendantPairGraph_not_adj_of_mem_distinct_components {C P : Type}
    {K : SimpleGraph (C ⊕ P)}
    {X Y : (PendantPairGraph K).ConnectedComponent} (hXY : X ≠ Y)
    {p q : P} (hp : p ∈ X.supp) (hq : q ∈ Y.supp) :
    ¬ K.Adj (Sum.inr p) (Sum.inr q) := by
  intro hpq
  have hqX : q ∈ X.supp := X.mem_supp_of_adj_mem_supp hp hpq
  exact hXY (SimpleGraph.ConnectedComponent.eq_of_common_vertex hqX hq)

lemma pendantPairGraph_vertices_ne_of_mem_distinct_components {C P : Type}
    {K : SimpleGraph (C ⊕ P)}
    {X Y : (PendantPairGraph K).ConnectedComponent} (hXY : X ≠ Y)
    {p q : P} (hp : p ∈ X.supp) (hq : q ∈ Y.supp) :
    p ≠ q := by
  intro hpq
  subst q
  exact hXY (SimpleGraph.ConnectedComponent.eq_of_common_vertex hp hq)

/-- Core vertices are close if there is a walk of length at most two between their core copies. -/
def CoreClose {C P : Type} (K : SimpleGraph (C ⊕ P)) (a b : C) : Prop :=
  ∃ p : K.Walk (Sum.inl a) (Sum.inl b), p.length ≤ 2

lemma CoreClose.refl {C P : Type} {K : SimpleGraph (C ⊕ P)} (a : C) :
    CoreClose K a a := by
  exact ⟨Walk.nil, by simp⟩

lemma CoreClose.symm {C P : Type} {K : SimpleGraph (C ⊕ P)} {a b : C}
    (h : CoreClose K a b) : CoreClose K b a := by
  rcases h with ⟨p, hp⟩
  exact ⟨p.reverse, by simpa [Walk.length_reverse] using hp⟩

lemma CoreClose.of_adj {C P : Type} {K : SimpleGraph (C ⊕ P)} {a b : C}
    (hab : K.Adj (Sum.inl a) (Sum.inl b)) : CoreClose K a b := by
  exact ⟨hab.toWalk, by simp⟩

lemma CoreClose.of_two_step {C P : Type} {K : SimpleGraph (C ⊕ P)} {a b : C}
    {z : C ⊕ P} (haz : K.Adj (Sum.inl a) z) (hzb : K.Adj z (Sum.inl b)) :
    CoreClose K a b := by
  exact ⟨Walk.cons haz hzb.toWalk, by simp⟩

lemma CoreClose.eq_or_adj_or_two_step {C P : Type} {K : SimpleGraph (C ⊕ P)} {a b : C}
    (h : CoreClose K a b) :
    a = b ∨ K.Adj (Sum.inl a) (Sum.inl b) ∨
      ∃ z : C ⊕ P, K.Adj (Sum.inl a) z ∧ K.Adj z (Sum.inl b) := by
  rcases h with ⟨w, hw⟩
  cases w with
  | nil => exact Or.inl rfl
  | cons h01 w₁ =>
      cases w₁ with
      | nil => exact Or.inr (Or.inl h01)
      | cons h12 w₂ =>
          cases w₂ with
          | nil => exact Or.inr (Or.inr ⟨_, h01, h12⟩)
          | cons h23 w₃ =>
              simp at hw
              omega

lemma CoreClose.adj_or_two_step_of_ne {C P : Type} {K : SimpleGraph (C ⊕ P)} {a b : C}
    (h : CoreClose K a b) (hab : a ≠ b) :
    K.Adj (Sum.inl a) (Sum.inl b) ∨
      ∃ z : C ⊕ P, K.Adj (Sum.inl a) z ∧ K.Adj z (Sum.inl b) := by
  rcases h.eq_or_adj_or_two_step with hEq | hAdj | hTwo
  · exact False.elim (hab hEq)
  · exact Or.inl hAdj
  · exact Or.inr hTwo

lemma CoreClose.two_step_of_ne_of_not_adj {C P : Type} {K : SimpleGraph (C ⊕ P)} {a b : C}
    (h : CoreClose K a b) (hab : a ≠ b) (hnadj : ¬ K.Adj (Sum.inl a) (Sum.inl b)) :
    ∃ z : C ⊕ P, K.Adj (Sum.inl a) z ∧ K.Adj z (Sum.inl b) := by
  rcases h.adj_or_two_step_of_ne hab with hAdj | hTwo
  · exact False.elim (hnadj hAdj)
  · exact hTwo

/-- The unordered distinct core pairs whose core copies are at graph distance at most two. -/
def CoreClosePairFinset {C P : Type} [Fintype C] (K : SimpleGraph (C ⊕ P)) : Finset (Sym2 C) := by
  classical
  exact Finset.univ.filter fun e : Sym2 C => ¬ e.IsDiag ∧ ∃ a b : C, e = s(a, b) ∧ CoreClose K a b

lemma mem_coreClosePairFinset_mk {C P : Type} [Fintype C] {K : SimpleGraph (C ⊕ P)}
    {a b : C} :
    s(a, b) ∈ CoreClosePairFinset K ↔ a ≠ b ∧ CoreClose K a b := by
  classical
  constructor
  · intro h
    rcases (by simpa [CoreClosePairFinset] using h) with ⟨hdiag, c, d, hcd, hclose⟩
    have hab : a ≠ b := by
      intro h
      exact hdiag (by simpa [Sym2.mk_isDiag_iff] using h)
    rcases hcd with ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · exact ⟨hab, by simpa [hac, hbd] using hclose⟩
    · have hba : CoreClose K b a := by simpa [hbc, had] using hclose
      exact ⟨hab, hba.symm⟩
  · rintro ⟨hab, hclose⟩
    simp [CoreClosePairFinset, hab]
    exact ⟨a, b, Or.inl ⟨rfl, rfl⟩, hclose⟩

/-- Core pairs with a common old core neighbor in the host graph. -/
def CoreOldTwoStepPairFinset {C : Type} [Fintype C] (H : SimpleGraph C) : Finset (Sym2 C) := by
  classical
  exact Finset.univ.filter fun e : Sym2 C =>
    ¬ e.IsDiag ∧ ∃ a : C, ∃ b : C, ∃ w : C, e = s(a, b) ∧ H.Adj w a ∧ H.Adj w b

lemma mem_coreOldTwoStepPairFinset_mk {C : Type} [Fintype C] {H : SimpleGraph C}
    {a b : C} :
    s(a, b) ∈ CoreOldTwoStepPairFinset H ↔
      a ≠ b ∧ ∃ w : C, H.Adj w a ∧ H.Adj w b := by
  classical
  constructor
  · intro h
    rcases (by simpa [CoreOldTwoStepPairFinset] using h) with
      ⟨hdiag, c, d, hcd, w, hwc, hwd⟩
    have hab : a ≠ b := by
      intro h
      exact hdiag (by simpa [Sym2.mk_isDiag_iff] using h)
    rcases hcd with ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · exact ⟨hab, w, by simpa [hac] using hwc, by simpa [hbd] using hwd⟩
    · exact ⟨hab, w, by simpa [had] using hwd, by simpa [hbc] using hwc⟩
  · rintro ⟨hab, w, hwa, hwb⟩
    simp [CoreOldTwoStepPairFinset, hab]
    exact ⟨a, b, Or.inl ⟨rfl, rfl⟩, w, hwa, hwb⟩

/-- The image of all ordered pairs of old neighbors of a common core vertex. -/
def NeighborPairImageFinset {C : Type} [Fintype C] (H : SimpleGraph C) : Finset (Sym2 C) := by
  classical
  exact Finset.univ.biUnion fun w : C =>
    (((H.neighborSet w).toFinset.product (H.neighborSet w).toFinset).image
      fun p : C × C => s(p.1, p.2))

lemma coreOldTwoStepPair_subset_neighborPairImage {C : Type} [Fintype C] {H : SimpleGraph C} :
    CoreOldTwoStepPairFinset H ⊆ NeighborPairImageFinset H := by
  classical
  intro e he
  rcases (by simpa [CoreOldTwoStepPairFinset] using he) with
    ⟨_hdiag, a, b, hpair, w, hwa, hwb⟩
  rw [hpair]
  rw [NeighborPairImageFinset]
  apply Finset.mem_biUnion.mpr
  refine ⟨w, by simp, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨(a, b), ?_, rfl⟩
  simpa [SimpleGraph.mem_neighborSet] using ⟨hwa, hwb⟩

lemma neighborPairImage_card_le_sum_neighbor_ncard {C : Type} [Fintype C] (H : SimpleGraph C) :
    (NeighborPairImageFinset H).card ≤
      ∑ w : C, (H.neighborSet w).ncard * (H.neighborSet w).ncard := by
  classical
  let imageAt := fun w : C =>
    (((H.neighborSet w).toFinset.product (H.neighborSet w).toFinset).image
      fun p : C × C => s(p.1, p.2))
  have hcard : (NeighborPairImageFinset H).card ≤ ∑ w : C, (imageAt w).card := by
    simpa [NeighborPairImageFinset, imageAt] using
      (Finset.card_biUnion_le (s := (Finset.univ : Finset C)) (t := imageAt))
  have hsum : (∑ w : C, (imageAt w).card) ≤
      ∑ w : C, (H.neighborSet w).ncard * (H.neighborSet w).ncard := by
    refine Finset.sum_le_sum ?_
    intro w _
    have himage : (imageAt w).card ≤
        ((H.neighborSet w).toFinset.product (H.neighborSet w).toFinset).card :=
      Finset.card_image_le
    have hprod : ((H.neighborSet w).toFinset.product (H.neighborSet w).toFinset).card =
        (H.neighborSet w).ncard * (H.neighborSet w).ncard := by
      simp [Finset.product_eq_sprod, Finset.card_product, Set.ncard_eq_toFinset_card']
    exact himage.trans_eq hprod
  exact hcard.trans hsum

lemma coreOldTwoStepPair_card_le_card_mul_sq {m d : ℕ} {H : SimpleGraph (Fin m)}
    (hdeg : MaxDegreeAtMost H d) :
    (CoreOldTwoStepPairFinset H).card ≤ m * d * d := by
  classical
  calc
    (CoreOldTwoStepPairFinset H).card ≤ (NeighborPairImageFinset H).card :=
      Finset.card_le_card coreOldTwoStepPair_subset_neighborPairImage
    _ ≤ ∑ w : Fin m, (H.neighborSet w).ncard * (H.neighborSet w).ncard :=
      neighborPairImage_card_le_sum_neighbor_ncard H
    _ ≤ ∑ _w : Fin m, d * d := by
      refine Finset.sum_le_sum ?_
      intro w _
      exact Nat.mul_le_mul (hdeg w) (hdeg w)
    _ = m * d * d := by
      simp [Fintype.card_fin]
      ring

/-- Distinct core pairs adjacent in a supergraph on `C ⊕ P`. -/
def CoreAdjPairFinset {C P : Type} [Fintype C] (K : SimpleGraph (C ⊕ P)) : Finset (Sym2 C) := by
  classical
  exact Finset.univ.filter fun e : Sym2 C =>
    ¬ e.IsDiag ∧ ∃ a : C, ∃ b : C, e = s(a, b) ∧ K.Adj (Sum.inl a) (Sum.inl b)

lemma mem_coreAdjPairFinset_mk {C P : Type} [Fintype C] {K : SimpleGraph (C ⊕ P)}
    {a b : C} :
    s(a, b) ∈ CoreAdjPairFinset K ↔ a ≠ b ∧ K.Adj (Sum.inl a) (Sum.inl b) := by
  classical
  constructor
  · intro h
    rcases (by simpa [CoreAdjPairFinset] using h) with ⟨hdiag, c, d, hcd, hKcd⟩
    have hab : a ≠ b := by
      intro h
      exact hdiag (by simpa [Sym2.mk_isDiag_iff] using h)
    rcases hcd with ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · exact ⟨hab, by simpa [hac, hbd] using hKcd⟩
    · exact ⟨hab, by simpa [had, hbc] using hKcd.symm⟩
  · rintro ⟨hab, hK⟩
    simp [CoreAdjPairFinset, hab]
    exact ⟨a, b, Or.inl ⟨rfl, rfl⟩, hK⟩

/-- Core-core adjacencies in `K` that were not old host edges. -/
def CoreNewAdjPairFinset {C P : Type} [Fintype C] (H : SimpleGraph C) (_root : P → C)
    (K : SimpleGraph (C ⊕ P)) : Finset (Sym2 C) := by
  classical
  exact Finset.univ.filter fun e : Sym2 C =>
    ¬ e.IsDiag ∧ ∃ a : C, ∃ b : C,
      e = s(a, b) ∧ K.Adj (Sum.inl a) (Sum.inl b) ∧ ¬ H.Adj a b

lemma mem_coreNewAdjPairFinset_mk {C P : Type} [Fintype C] {H : SimpleGraph C}
    {root : P → C} {K : SimpleGraph (C ⊕ P)} {a b : C} :
    s(a, b) ∈ CoreNewAdjPairFinset H root K ↔
      a ≠ b ∧ K.Adj (Sum.inl a) (Sum.inl b) ∧ ¬ H.Adj a b := by
  classical
  constructor
  · intro h
    rcases (by simpa [CoreNewAdjPairFinset] using h) with ⟨hdiag, c, d, hcd, hKcd, hHcd⟩
    have hab : a ≠ b := by
      intro h
      exact hdiag (by simpa [Sym2.mk_isDiag_iff] using h)
    rcases hcd with ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · exact ⟨hab, by simpa [hac, hbd] using hKcd, by simpa [hac, hbd] using hHcd⟩
    · exact ⟨hab, by simpa [had, hbc] using hKcd.symm,
        by simpa [had, hbc, adj_comm] using hHcd⟩
  · rintro ⟨hab, hK, hH⟩
    simp [CoreNewAdjPairFinset, hab]
    exact ⟨a, b, Or.inl ⟨rfl, rfl⟩, hK, hH⟩



lemma coreFree_components_coreClose_of_two_step {C P : Type}
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X Y : (PendantPairGraph K).ConnectedComponent}
    (hXfree : PendantComponentCoreFree K root X)
    (hYfree : PendantComponentCoreFree K root Y) (hXY : X ≠ Y)
    {p q : P} (hp : p ∈ X.supp) (hq : q ∈ Y.supp)
    {z : C ⊕ P} (hpz : K.Adj (Sum.inr p) z) (hzq : K.Adj z (Sum.inr q)) :
    CoreClose K (root p) (root q) := by
  cases z with
  | inl c =>
      have hpc : c = root p := hXfree p hp c hpz
      have hqc : c = root q := hYfree q hq c hzq.symm
      have hroot : root p = root q := hpc.symm.trans hqc
      simpa [hroot] using CoreClose.refl (K := K) (root p)
  | inr r =>
      have hrX : r ∈ X.supp := X.mem_supp_of_adj_mem_supp hp hpz
      have hrY : r ∈ Y.supp := Y.mem_supp_of_adj_mem_supp hq hzq.symm
      exact False.elim (hXY (SimpleGraph.ConnectedComponent.eq_of_common_vertex hrX hrY))

lemma coreFree_components_exists_coreClose_of_three_step {C P : Type}
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X Y : (PendantPairGraph K).ConnectedComponent}
    (hXfree : PendantComponentCoreFree K root X)
    (hYfree : PendantComponentCoreFree K root Y) (hXY : X ≠ Y)
    {p q : P} (hp : p ∈ X.supp) (hq : q ∈ Y.supp)
    {z₁ z₂ : C ⊕ P} (h01 : K.Adj (Sum.inr p) z₁)
    (h12 : K.Adj z₁ z₂) (h23 : K.Adj z₂ (Sum.inr q)) :
    ∃ u : P, u ∈ X.supp ∧ ∃ v : P, v ∈ Y.supp ∧ CoreClose K (root u) (root v) := by
  cases z₁ with
  | inl c₁ =>
      cases z₂ with
      | inl c₂ =>
          refine ⟨p, hp, q, hq, ?_⟩
          have hc₁ : c₁ = root p := hXfree p hp c₁ h01
          have hc₂ : c₂ = root q := hYfree q hq c₂ h23.symm
          exact CoreClose.of_adj (by simpa [hc₁, hc₂] using h12)
      | inr r₂ =>
          have hc₁p : c₁ = root p := hXfree p hp c₁ h01
          have hr₂Y : r₂ ∈ Y.supp := Y.mem_supp_of_adj_mem_supp hq h23.symm
          have hc₁r₂ : c₁ = root r₂ := hYfree r₂ hr₂Y c₁ h12.symm
          refine ⟨p, hp, r₂, hr₂Y, ?_⟩
          have hroot : root p = root r₂ := hc₁p.symm.trans hc₁r₂
          simpa [hroot] using CoreClose.refl (K := K) (root p)
  | inr r₁ =>
      cases z₂ with
      | inl c₂ =>
          have hr₁X : r₁ ∈ X.supp := X.mem_supp_of_adj_mem_supp hp h01
          have hc₂r₁ : c₂ = root r₁ := hXfree r₁ hr₁X c₂ h12
          have hc₂q : c₂ = root q := hYfree q hq c₂ h23.symm
          refine ⟨r₁, hr₁X, q, hq, ?_⟩
          have hroot : root r₁ = root q := hc₂r₁.symm.trans hc₂q
          simpa [hroot] using CoreClose.refl (K := K) (root r₁)
      | inr r₂ =>
          have hr₁X : r₁ ∈ X.supp := X.mem_supp_of_adj_mem_supp hp h01
          have hr₂X : r₂ ∈ X.supp := X.mem_supp_of_adj_mem_supp hr₁X h12
          have hr₂Y : r₂ ∈ Y.supp := Y.mem_supp_of_adj_mem_supp hq h23.symm
          exact False.elim (hXY (SimpleGraph.ConnectedComponent.eq_of_common_vertex hr₂X hr₂Y))

lemma coreFree_components_exists_coreClose_of_four_step {C P : Type}
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X Y : (PendantPairGraph K).ConnectedComponent}
    (hXfree : PendantComponentCoreFree K root X)
    (hYfree : PendantComponentCoreFree K root Y) (hXY : X ≠ Y)
    {p q : P} (hp : p ∈ X.supp) (hq : q ∈ Y.supp)
    {z₁ z₂ z₃ : C ⊕ P} (h01 : K.Adj (Sum.inr p) z₁)
    (h12 : K.Adj z₁ z₂) (h23 : K.Adj z₂ z₃)
    (h34 : K.Adj z₃ (Sum.inr q)) :
    ∃ u : P, u ∈ X.supp ∧ ∃ v : P, v ∈ Y.supp ∧ CoreClose K (root u) (root v) := by
  cases z₁ with
  | inl c₁ =>
      cases z₂ with
      | inl c₂ =>
          cases z₃ with
          | inl c₃ =>
              refine ⟨p, hp, q, hq, ?_⟩
              have hc₁ : c₁ = root p := hXfree p hp c₁ h01
              have hc₃ : c₃ = root q := hYfree q hq c₃ h34.symm
              exact CoreClose.of_two_step (by simpa [hc₁] using h12) (by simpa [hc₃] using h23)
          | inr r₃ =>
              have hc₁ : c₁ = root p := hXfree p hp c₁ h01
              have hr₃Y : r₃ ∈ Y.supp := Y.mem_supp_of_adj_mem_supp hq h34.symm
              have hc₂r₃ : c₂ = root r₃ := hYfree r₃ hr₃Y c₂ h23.symm
              refine ⟨p, hp, r₃, hr₃Y, ?_⟩
              exact CoreClose.of_adj (by simpa [hc₁, hc₂r₃] using h12)
      | inr r₂ =>
          cases z₃ with
          | inl c₃ =>
              refine ⟨p, hp, q, hq, ?_⟩
              have hc₁p : c₁ = root p := hXfree p hp c₁ h01
              have hc₃q : c₃ = root q := hYfree q hq c₃ h34.symm
              exact CoreClose.of_two_step (by simpa [hc₁p] using h12) (by simpa [hc₃q] using h23)
          | inr r₃ =>
              have hc₁p : c₁ = root p := hXfree p hp c₁ h01
              have hr₃Y : r₃ ∈ Y.supp := Y.mem_supp_of_adj_mem_supp hq h34.symm
              have hr₂Y : r₂ ∈ Y.supp := Y.mem_supp_of_adj_mem_supp hr₃Y h23.symm
              have hc₁r₂ : c₁ = root r₂ := hYfree r₂ hr₂Y c₁ h12.symm
              refine ⟨p, hp, r₂, hr₂Y, ?_⟩
              have hroot : root p = root r₂ := hc₁p.symm.trans hc₁r₂
              simpa [hroot] using CoreClose.refl (K := K) (root p)
  | inr r₁ =>
      cases z₂ with
      | inl c₂ =>
          cases z₃ with
          | inl c₃ =>
              have hr₁X : r₁ ∈ X.supp := X.mem_supp_of_adj_mem_supp hp h01
              have hc₂r₁ : c₂ = root r₁ := hXfree r₁ hr₁X c₂ h12
              have hc₃q : c₃ = root q := hYfree q hq c₃ h34.symm
              refine ⟨r₁, hr₁X, q, hq, ?_⟩
              exact CoreClose.of_adj (by simpa [hc₂r₁, hc₃q] using h23)
          | inr r₃ =>
              have hr₁X : r₁ ∈ X.supp := X.mem_supp_of_adj_mem_supp hp h01
              have hc₂r₁ : c₂ = root r₁ := hXfree r₁ hr₁X c₂ h12
              have hr₃Y : r₃ ∈ Y.supp := Y.mem_supp_of_adj_mem_supp hq h34.symm
              have hc₂r₃ : c₂ = root r₃ := hYfree r₃ hr₃Y c₂ h23.symm
              refine ⟨r₁, hr₁X, r₃, hr₃Y, ?_⟩
              have hroot : root r₁ = root r₃ := hc₂r₁.symm.trans hc₂r₃
              simpa [hroot] using CoreClose.refl (K := K) (root r₁)
      | inr r₂ =>
          cases z₃ with
          | inl c₃ =>
              have hr₁X : r₁ ∈ X.supp := X.mem_supp_of_adj_mem_supp hp h01
              have hr₂X : r₂ ∈ X.supp := X.mem_supp_of_adj_mem_supp hr₁X h12
              have hc₃r₂ : c₃ = root r₂ := hXfree r₂ hr₂X c₃ h23
              have hc₃q : c₃ = root q := hYfree q hq c₃ h34.symm
              refine ⟨r₂, hr₂X, q, hq, ?_⟩
              have hroot : root r₂ = root q := hc₃r₂.symm.trans hc₃q
              simpa [hroot] using CoreClose.refl (K := K) (root r₂)
          | inr r₃ =>
              have hr₁X : r₁ ∈ X.supp := X.mem_supp_of_adj_mem_supp hp h01
              have hr₂X : r₂ ∈ X.supp := X.mem_supp_of_adj_mem_supp hr₁X h12
              have hr₃X : r₃ ∈ X.supp := X.mem_supp_of_adj_mem_supp hr₂X h23
              have hr₃Y : r₃ ∈ Y.supp := Y.mem_supp_of_adj_mem_supp hq h34.symm
              exact False.elim (hXY (SimpleGraph.ConnectedComponent.eq_of_common_vertex hr₃X hr₃Y))

lemma coreFree_components_exists_coreClose_of_walk_le_four {C P : Type}
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X Y : (PendantPairGraph K).ConnectedComponent}
    (hXfree : PendantComponentCoreFree K root X)
    (hYfree : PendantComponentCoreFree K root Y) (hXY : X ≠ Y)
    {p q : P} (hp : p ∈ X.supp) (hq : q ∈ Y.supp)
    (w : K.Walk (Sum.inr p) (Sum.inr q)) (hw : w.length ≤ 4) :
    ∃ u : P, u ∈ X.supp ∧ ∃ v : P, v ∈ Y.supp ∧ CoreClose K (root u) (root v) := by
  cases w with
  | nil =>
      exact False.elim (hXY (SimpleGraph.ConnectedComponent.eq_of_common_vertex hp hq))
  | cons h01 w₁ =>
      cases w₁ with
      | nil =>
          exact False.elim ((pendantPairGraph_not_adj_of_mem_distinct_components hXY hp hq) h01)
      | cons h12 w₂ =>
          cases w₂ with
          | nil =>
              exact ⟨p, hp, q, hq,
                coreFree_components_coreClose_of_two_step hXfree hYfree hXY hp hq h01 h12⟩
          | cons h23 w₃ =>
              cases w₃ with
              | nil =>
                  exact coreFree_components_exists_coreClose_of_three_step
                    hXfree hYfree hXY hp hq h01 h12 h23
              | cons h34 w₄ =>
                  cases w₄ with
                  | nil =>
                      exact coreFree_components_exists_coreClose_of_four_step
                        hXfree hYfree hXY hp hq h01 h12 h23 h34
                  | cons h45 w₅ =>
                      simp at hw
                      omega

/-- Lemma 1 from the write-up, in the form needed for counting: distinct core-free
pendant-pair components force a pair of roots to be within two steps in the supergraph. -/
lemma coreFree_components_exists_coreClose_of_ediam_le_four {C P : Type}
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X Y : (PendantPairGraph K).ConnectedComponent}
    (hKdiam : K.ediam ≤ (4 : ℕ∞))
    (hXfree : PendantComponentCoreFree K root X)
    (hYfree : PendantComponentCoreFree K root Y) (hXY : X ≠ Y) :
    ∃ u : P, u ∈ X.supp ∧ ∃ v : P, v ∈ Y.supp ∧ CoreClose K (root u) (root v) := by
  rcases X.nonempty_supp with ⟨p, hp⟩
  rcases Y.nonempty_supp with ⟨q, hq⟩
  have hed : K.edist (Sum.inr p) (Sum.inr q) ≤ (4 : ℕ∞) :=
    (SimpleGraph.ediam_le_iff.mp hKdiam) (Sum.inr p) (Sum.inr q)
  rcases exists_walk_length_le_of_edist_le hed with ⟨w, hw⟩
  exact coreFree_components_exists_coreClose_of_walk_le_four hXfree hYfree hXY hp hq w hw

/-- The new edges of `K` over a base graph `G`, as a finset matching `addedEdgeCount`. -/
def AddedEdgeFinset {V : Type} [Fintype V] (G K : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact K.edgeFinset \ G.edgeFinset

@[simp] lemma mem_addedEdgeFinset {V : Type} [Fintype V] {G K : SimpleGraph V}
    {e : Sym2 V} :
    e ∈ AddedEdgeFinset G K ↔ e ∈ K.edgeSet ∧ e ∉ G.edgeSet := by
  classical
  simp [AddedEdgeFinset]

@[simp] lemma addedEdgeCount_eq_addedEdgeFinset {n : ℕ} (G K : SimpleGraph (Fin n)) :
    addedEdgeCount G K = (AddedEdgeFinset G K).card := by
  classical
  unfold addedEdgeCount AddedEdgeFinset
  congr 1
  ext e
  simp

lemma coreNewAdjPair_card_le_addedEdgeFinset {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)} :
    (CoreNewAdjPairFinset H root K).card ≤
      (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
  classical
  let cinl : C ↪ C ⊕ P := Function.Embedding.inl
  let f : {e : Sym2 C // e ∈ CoreNewAdjPairFinset H root K} →
      {e : Sym2 (C ⊕ P) // e ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K} := fun e =>
    ⟨cinl.sym2Map e.1, by
      refine Sym2.ind ?_ e.1 e.2
      intro a b heab
      rcases (mem_coreNewAdjPairFinset_mk (H := H) (root := root) (K := K)).mp heab with
        ⟨_hab, hK, hH⟩
      rw [mem_addedEdgeFinset]
      constructor
      · simpa [cinl, Function.Embedding.sym2Map_apply, Sym2.map_pair_eq,
          SimpleGraph.mem_edgeSet] using hK
      · intro hbase
        apply hH
        simpa [cinl, Function.Embedding.sym2Map_apply, Sym2.map_pair_eq,
          SimpleGraph.mem_edgeSet] using hbase⟩
  have hf : Function.Injective f := by
    intro e₁ e₂ h
    apply Subtype.ext
    have hval : cinl.sym2Map e₁.1 = cinl.sym2Map e₂.1 := by
      simpa [f] using congrArg Subtype.val h
    exact cinl.sym2Map.injective hval
  have hcard := Nat.card_le_card_of_injective f hf
  have hdom : Nat.card {e : Sym2 C // e ∈ CoreNewAdjPairFinset H root K} =
      (CoreNewAdjPairFinset H root K).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have hcod : Nat.card {e : Sym2 (C ⊕ P) // e ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K} =
      (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hdom, hcod] at hcard
  exact hcard

lemma coreAdjPair_card_le_host_edges_add_added {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)} :
    (CoreAdjPairFinset K).card ≤
      Nat.card H.edgeSet + (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
  classical
  have hsubset : CoreAdjPairFinset K ⊆ H.edgeFinset ∪ CoreNewAdjPairFinset H root K := by
    intro e he
    rcases (by simpa [CoreAdjPairFinset] using he) with ⟨hdiag, a, b, hpair, hK⟩
    by_cases hH : H.Adj a b
    · apply Finset.mem_union.mpr
      left
      rw [hpair]
      simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hH
    · apply Finset.mem_union.mpr
      right
      rw [CoreNewAdjPairFinset]
      simp [hdiag]
      exact ⟨a, b, hpair, hK, hH⟩
  have hcard_union : (CoreAdjPairFinset K).card ≤
      (H.edgeFinset ∪ CoreNewAdjPairFinset H root K).card := Finset.card_le_card hsubset
  have hunion : (H.edgeFinset ∪ CoreNewAdjPairFinset H root K).card ≤
      H.edgeFinset.card + (CoreNewAdjPairFinset H root K).card := Finset.card_union_le _ _
  have hnew := coreNewAdjPair_card_le_addedEdgeFinset (H := H) (root := root) (K := K)
  have hedge : H.edgeFinset.card = Nat.card H.edgeSet := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  omega

/-- Oriented new edges whose terminal endpoint is a core vertex.  These are the charges used for
non-old distance-two close pairs. -/
def CoreIncidentNewOrientationFinset {C P : Type} [Fintype C] [Fintype P]
    (H : SimpleGraph C) (root : P → C) (K : SimpleGraph (C ⊕ P)) : Finset ((C ⊕ P) × C) := by
  classical
  exact Finset.univ.filter fun oa : (C ⊕ P) × C =>
    K.Adj oa.1 (Sum.inl oa.2) ∧
      s(oa.1, Sum.inl oa.2) ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K

@[simp] lemma mem_coreIncidentNewOrientationFinset {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)} {z : C ⊕ P} {a : C} :
    (z, a) ∈ CoreIncidentNewOrientationFinset H root K ↔
      K.Adj z (Sum.inl a) ∧
        s(z, Sum.inl a) ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K := by
  classical
  simp [CoreIncidentNewOrientationFinset]

/-- The overcounting set of charged close core pairs. -/
def CoreChargedPairFinset {C P : Type} [Fintype C] [Fintype P]
    (H : SimpleGraph C) (root : P → C) (K : SimpleGraph (C ⊕ P)) : Finset (Sym2 C) := by
  classical
  exact (CoreIncidentNewOrientationFinset H root K).biUnion fun oa =>
    (CoreNeighborFinset K oa.1).image fun b : C => s(oa.2, b)

lemma mem_coreChargedPairFinset_of_orientation {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)}
    {z : C ⊕ P} {a b : C}
    (hnew : (z, a) ∈ CoreIncidentNewOrientationFinset H root K)
    (hzb : K.Adj z (Sum.inl b)) :
    s(a, b) ∈ CoreChargedPairFinset H root K := by
  classical
  rw [CoreChargedPairFinset]
  apply Finset.mem_biUnion.mpr
  refine ⟨(z, a), hnew, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨b, by simpa using hzb, rfl⟩

lemma base_core_two_step_of_base_neighbors {C P : Type} {H : SimpleGraph C} {root : P → C}
    {z : C ⊕ P} {a b : C} (hab : a ≠ b)
    (hza : (PendantCoreGraphSum H root).Adj z (Sum.inl a))
    (hzb : (PendantCoreGraphSum H root).Adj z (Sum.inl b)) :
    ∃ w : C, H.Adj w a ∧ H.Adj w b := by
  cases z with
  | inl w =>
      exact ⟨w, by simpa using hza, by simpa using hzb⟩
  | inr p =>
      have ha : a = root p := by simpa using hza
      have hb : b = root p := by simpa using hzb
      exact False.elim (hab (ha.trans hb.symm))

lemma coreClosePair_subset_adj_old_charged {C P : Type} [Fintype C] [Fintype P] [DecidableEq C]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)} :
    CoreClosePairFinset K ⊆
      (CoreAdjPairFinset K ∪ CoreOldTwoStepPairFinset H) ∪ CoreChargedPairFinset H root K := by
  classical
  intro e he
  refine Sym2.ind ?_ e he
  intro a b heab
  rcases (mem_coreClosePairFinset_mk (K := K)).mp heab with ⟨hab, hclose⟩
  rcases hclose.adj_or_two_step_of_ne hab with hAdj | hTwo
  · apply Finset.mem_union.mpr
    left
    apply Finset.mem_union.mpr
    left
    exact (mem_coreAdjPairFinset_mk (K := K)).mpr ⟨hab, hAdj⟩
  · rcases hTwo with ⟨z, haz, hzb⟩
    have hza : K.Adj z (Sum.inl a) := haz.symm
    by_cases hbaseza : (PendantCoreGraphSum H root).Adj z (Sum.inl a)
    · by_cases hbasezb : (PendantCoreGraphSum H root).Adj z (Sum.inl b)
      · rcases base_core_two_step_of_base_neighbors (H := H) (root := root) hab hbaseza hbasezb with
          ⟨w, hwa, hwb⟩
        apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        right
        exact (mem_coreOldTwoStepPairFinset_mk (H := H)).mpr ⟨hab, w, hwa, hwb⟩
      · have hadded : s(z, Sum.inl b) ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K := by
          rw [mem_addedEdgeFinset]
          constructor
          · simpa [SimpleGraph.mem_edgeSet] using hzb
          · intro hbaseEdge
            exact hbasezb (by simpa [SimpleGraph.mem_edgeSet] using hbaseEdge)
        have horient : (z, b) ∈ CoreIncidentNewOrientationFinset H root K := by
          exact
            (mem_coreIncidentNewOrientationFinset (H := H) (root := root)
              (K := K)).mpr ⟨hzb, hadded⟩
        apply Finset.mem_union.mpr
        right
        simpa [Sym2.eq_swap] using mem_coreChargedPairFinset_of_orientation (H := H)
          (root := root) (K := K) horient hza
    · have hadded : s(z, Sum.inl a) ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K := by
        rw [mem_addedEdgeFinset]
        constructor
        · simpa [SimpleGraph.mem_edgeSet] using hza
        · intro hbaseEdge
          exact hbaseza (by simpa [SimpleGraph.mem_edgeSet] using hbaseEdge)
      have horient : (z, a) ∈ CoreIncidentNewOrientationFinset H root K := by
        exact
          (mem_coreIncidentNewOrientationFinset (H := H) (root := root)
            (K := K)).mpr ⟨hza, hadded⟩
      apply Finset.mem_union.mpr
      right
      exact mem_coreChargedPairFinset_of_orientation (H := H) (root := root) (K := K) horient hzb

lemma coreChargedPair_card_le_orientation_mul_indepNum {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)}
    (hGK : PendantCoreGraphSum H root ≤ K) (hKtf : K.CliqueFree 3) :
    (CoreChargedPairFinset H root K).card ≤
      (CoreIncidentNewOrientationFinset H root K).card * H.indepNum := by
  classical
  let orient := CoreIncidentNewOrientationFinset H root K
  let imageAt := fun oa : (C ⊕ P) × C =>
    (CoreNeighborFinset K oa.1).image fun b : C => s(oa.2, b)
  have hcard :
      (CoreChargedPairFinset H root K).card ≤ ∑ oa ∈ orient, (imageAt oa).card := by
    simpa [CoreChargedPairFinset, orient, imageAt] using
      (Finset.card_biUnion_le (s := orient) (t := imageAt))
  have hsum : (∑ oa ∈ orient, (imageAt oa).card) ≤ ∑ _oa ∈ orient, H.indepNum := by
    refine Finset.sum_le_sum ?_
    intro oa _
    exact (Finset.card_image_le.trans
      (coreNeighborFinset_card_le_indepNum_of_pendantCore_le hGK hKtf oa.1))
  calc
    (CoreChargedPairFinset H root K).card ≤ ∑ oa ∈ orient, (imageAt oa).card := hcard
    _ ≤ ∑ _oa ∈ orient, H.indepNum := hsum
    _ = orient.card * H.indepNum := by simp [Finset.sum_const]



/-- Endpoints of a finset of unordered pairs, counted with the pair they belong to. -/
def Sym2EndpointFinset {V : Type} (E : Finset (Sym2 V)) : Finset (Sym2 V × V) := by
  classical
  exact E.biUnion fun e => e.toFinset.image fun v => (e, v)

@[simp] lemma mem_sym2EndpointFinset {V : Type} {E : Finset (Sym2 V)} {e : Sym2 V} {v : V} :
    (e, v) ∈ Sym2EndpointFinset E ↔ e ∈ E ∧ v ∈ e := by
  classical
  constructor
  · intro h
    rw [Sym2EndpointFinset] at h
    rcases Finset.mem_biUnion.mp h with ⟨e', he', hv⟩
    rcases Finset.mem_image.mp hv with ⟨v', hv', hpair⟩
    cases hpair
    exact ⟨he', by simpa [Sym2.mem_toFinset] using hv'⟩
  · rintro ⟨he, hv⟩
    rw [Sym2EndpointFinset]
    apply Finset.mem_biUnion.mpr
    refine ⟨e, he, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨v, by simpa [Sym2.mem_toFinset] using hv, rfl⟩

lemma sym2EndpointFinset_card_le_two_mul {V : Type} (E : Finset (Sym2 V)) :
    (Sym2EndpointFinset E).card ≤ 2 * E.card := by
  classical
  let endpoints := fun e : Sym2 V => e.toFinset.image fun v => (e, v)
  have hcard : (Sym2EndpointFinset E).card ≤ ∑ e ∈ E, (endpoints e).card := by
    simpa [Sym2EndpointFinset, endpoints] using
      (Finset.card_biUnion_le (s := E) (t := endpoints))
  have hsum : (∑ e ∈ E, (endpoints e).card) ≤ ∑ _e ∈ E, 2 := by
    refine Finset.sum_le_sum ?_
    intro e _
    have himage : (endpoints e).card ≤ e.toFinset.card := by
      simpa [endpoints] using (Finset.card_image_le (s := e.toFinset) (f := fun v => (e, v)))
    have hto : e.toFinset.card ≤ 2 := by
      rw [Sym2.card_toFinset]
      split <;> omega
    exact himage.trans hto
  calc
    (Sym2EndpointFinset E).card ≤ ∑ e ∈ E, (endpoints e).card := hcard
    _ ≤ ∑ _e ∈ E, 2 := hsum
    _ = E.card * 2 := by simp [Finset.sum_const]
    _ = 2 * E.card := by rw [Nat.mul_comm]


/-- Ordered distinct core pairs whose unordered pair is close. -/
def CoreCloseOrderedPairFinset {C P : Type} [Fintype C]
    (K : SimpleGraph (C ⊕ P)) : Finset (C × C) := by
  classical
  exact Finset.univ.filter fun ab : C × C => ab.1 ≠ ab.2 ∧ s(ab.1, ab.2) ∈ CoreClosePairFinset K

@[simp] lemma mem_coreCloseOrderedPairFinset {C P : Type} [Fintype C]
    {K : SimpleGraph (C ⊕ P)} {a b : C} :
    (a, b) ∈ CoreCloseOrderedPairFinset K ↔ a ≠ b ∧ s(a, b) ∈ CoreClosePairFinset K := by
  classical
  simp [CoreCloseOrderedPairFinset]

lemma coreCloseOrderedPair_card_le_two_mul {C P : Type} [Fintype C]
    {K : SimpleGraph (C ⊕ P)} :
    (CoreCloseOrderedPairFinset K).card ≤ 2 * (CoreClosePairFinset K).card := by
  classical
  let endpoints := Sym2EndpointFinset (CoreClosePairFinset K)
  let f : {ab : C × C // ab ∈ CoreCloseOrderedPairFinset K} →
      {ev : Sym2 C × C // ev ∈ endpoints} := fun ab =>
    ⟨(s(ab.1.1, ab.1.2), ab.1.1), by
      change (s(ab.1.1, ab.1.2), ab.1.1) ∈ Sym2EndpointFinset (CoreClosePairFinset K)
      rw [mem_sym2EndpointFinset]
      exact ⟨(mem_coreCloseOrderedPairFinset (K := K)).mp ab.2 |>.2,
        Sym2.mem_mk_left _ _⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨a₁, b₁⟩, h₁⟩ ⟨⟨a₂, b₂⟩, h₂⟩ h
    apply Subtype.ext
    have hpair : (s(a₁, b₁), a₁) = (s(a₂, b₂), a₂) := by
      simpa [f] using congrArg Subtype.val h
    have ha : a₁ = a₂ := congrArg Prod.snd hpair
    have hedge : s(a₁, b₁) = s(a₂, b₂) := congrArg Prod.fst hpair
    have hb : b₁ = b₂ := by
      have hedge' : s(a₁, b₁) = s(a₁, b₂) := by
        simpa [ha] using hedge
      exact Sym2.congr_right.mp hedge'
    simp [ha, hb]
  have hcard := Nat.card_le_card_of_injective f hf
  have hdom : Nat.card {ab : C × C // ab ∈ CoreCloseOrderedPairFinset K} =
      (CoreCloseOrderedPairFinset K).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have hcod : Nat.card {ev : Sym2 C × C // ev ∈ endpoints} = endpoints.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hdom, hcod] at hcard
  exact hcard.trans (sym2EndpointFinset_card_le_two_mul (CoreClosePairFinset K))

/-- Endpoints of new edges, counted with the edge they belong to. -/
def AddedEdgeEndpointFinset {V : Type} [Fintype V]
    (G K : SimpleGraph V) : Finset (Sym2 V × V) := by
  classical
  exact (AddedEdgeFinset G K).biUnion fun e => e.toFinset.image fun v => (e, v)

@[simp] lemma mem_addedEdgeEndpointFinset {V : Type} [Fintype V]
    {G K : SimpleGraph V} {e : Sym2 V} {v : V} :
    (e, v) ∈ AddedEdgeEndpointFinset G K ↔ e ∈ AddedEdgeFinset G K ∧ v ∈ e := by
  classical
  constructor
  · intro h
    rw [AddedEdgeEndpointFinset] at h
    rcases Finset.mem_biUnion.mp h with ⟨e', he', hv⟩
    rcases Finset.mem_image.mp hv with ⟨v', hv', hpair⟩
    cases hpair
    exact ⟨he', by simpa [Sym2.mem_toFinset] using hv'⟩
  · rintro ⟨he, hv⟩
    rw [AddedEdgeEndpointFinset]
    apply Finset.mem_biUnion.mpr
    refine ⟨e, he, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨v, by simpa [Sym2.mem_toFinset] using hv, rfl⟩

lemma addedEdgeEndpointFinset_card_le_two_mul {V : Type} [Fintype V]
    (G K : SimpleGraph V) :
    (AddedEdgeEndpointFinset G K).card ≤ 2 * (AddedEdgeFinset G K).card := by
  classical
  let endpoints := fun e : Sym2 V => e.toFinset.image fun v => (e, v)
  have hcard : (AddedEdgeEndpointFinset G K).card ≤
      ∑ e ∈ AddedEdgeFinset G K, (endpoints e).card := by
    simpa [AddedEdgeEndpointFinset, endpoints] using
      (Finset.card_biUnion_le (s := AddedEdgeFinset G K) (t := endpoints))
  have hsum : (∑ e ∈ AddedEdgeFinset G K, (endpoints e).card) ≤
      ∑ _e ∈ AddedEdgeFinset G K, 2 := by
    refine Finset.sum_le_sum ?_
    intro e _
    have himage : (endpoints e).card ≤ e.toFinset.card := by
      simpa [endpoints] using (Finset.card_image_le (s := e.toFinset) (f := fun v => (e, v)))
    have hto : e.toFinset.card ≤ 2 := by
      rw [Sym2.card_toFinset]
      split <;> omega
    exact himage.trans hto
  calc
    (AddedEdgeEndpointFinset G K).card ≤
        ∑ e ∈ AddedEdgeFinset G K, (endpoints e).card := hcard
    _ ≤ ∑ _e ∈ AddedEdgeFinset G K, 2 := hsum
    _ = (AddedEdgeFinset G K).card * 2 := by simp [Finset.sum_const]
    _ = 2 * (AddedEdgeFinset G K).card := by rw [Nat.mul_comm]

lemma coreIncidentNewOrientation_card_le_two_mul_added {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)} :
    (CoreIncidentNewOrientationFinset H root K).card ≤
      2 * (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
  classical
  let endpointSet := AddedEdgeEndpointFinset (PendantCoreGraphSum H root) K
  let f : {oa : (C ⊕ P) × C // oa ∈ CoreIncidentNewOrientationFinset H root K} →
      {ev : Sym2 (C ⊕ P) × (C ⊕ P) // ev ∈ endpointSet} := fun oa =>
    ⟨(s(oa.1.1, Sum.inl oa.1.2), Sum.inl oa.1.2), by
      change (s(oa.1.1, Sum.inl oa.1.2), Sum.inl oa.1.2) ∈
        AddedEdgeEndpointFinset (PendantCoreGraphSum H root) K
      rw [mem_addedEdgeEndpointFinset]
      exact ⟨(mem_coreIncidentNewOrientationFinset (H := H) (root := root) (K := K)).mp oa.2 |>.2,
        Sym2.mem_mk_right _ _⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨z₁, a₁⟩, h₁⟩ ⟨⟨z₂, a₂⟩, h₂⟩ h
    apply Subtype.ext
    have hpair : (s(z₁, (Sum.inl a₁ : C ⊕ P)), (Sum.inl a₁ : C ⊕ P)) =
        (s(z₂, (Sum.inl a₂ : C ⊕ P)), (Sum.inl a₂ : C ⊕ P)) := by
      simpa [f] using congrArg Subtype.val h
    have ha : a₁ = a₂ := Sum.inl.inj (congrArg Prod.snd hpair)
    have hedge : s(z₁, (Sum.inl a₁ : C ⊕ P)) = s(z₂, (Sum.inl a₂ : C ⊕ P)) :=
      congrArg Prod.fst hpair
    have hz : z₁ = z₂ := by
      have hedge' : s(z₁, (Sum.inl a₁ : C ⊕ P)) = s(z₂, (Sum.inl a₁ : C ⊕ P)) := by
        simpa [ha] using hedge
      exact Sym2.congr_left.mp hedge'
    simp [hz, ha]
  have hcard := Nat.card_le_card_of_injective f hf
  have hdom : Nat.card {oa : (C ⊕ P) × C // oa ∈ CoreIncidentNewOrientationFinset H root K} =
      (CoreIncidentNewOrientationFinset H root K).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have hcod : Nat.card {ev : Sym2 (C ⊕ P) × (C ⊕ P) // ev ∈ endpointSet} =
      endpointSet.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hdom, hcod] at hcard
  exact hcard.trans (addedEdgeEndpointFinset_card_le_two_mul (PendantCoreGraphSum H root) K)

lemma coreChargedPair_card_le_two_mul_added_mul_indepNum {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)}
    (hGK : PendantCoreGraphSum H root ≤ K) (hKtf : K.CliqueFree 3) :
    (CoreChargedPairFinset H root K).card ≤
      2 * (AddedEdgeFinset (PendantCoreGraphSum H root) K).card * H.indepNum := by
  have hcharged := coreChargedPair_card_le_orientation_mul_indepNum (H := H) (root := root)
    (K := K) hGK hKtf
  have horient := coreIncidentNewOrientation_card_le_two_mul_added (H := H) (root := root) (K := K)
  exact hcharged.trans (Nat.mul_le_mul_right H.indepNum horient)

lemma coreClosePair_card_le_adj_old_charged {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)} :
    (CoreClosePairFinset K).card ≤
      (CoreAdjPairFinset K).card + (CoreOldTwoStepPairFinset H).card +
        (CoreChargedPairFinset H root K).card := by
  classical
  have hsubset := coreClosePair_subset_adj_old_charged (C := C) (P := P)
    (H := H) (root := root) (K := K)
  have hcard : (CoreClosePairFinset K).card ≤
      ((CoreAdjPairFinset K ∪ CoreOldTwoStepPairFinset H) ∪
        CoreChargedPairFinset H root K).card := Finset.card_le_card hsubset
  have houter : ((CoreAdjPairFinset K ∪ CoreOldTwoStepPairFinset H) ∪
        CoreChargedPairFinset H root K).card ≤
      (CoreAdjPairFinset K ∪ CoreOldTwoStepPairFinset H).card +
        (CoreChargedPairFinset H root K).card := Finset.card_union_le _ _
  have hinner : (CoreAdjPairFinset K ∪ CoreOldTwoStepPairFinset H).card ≤
      (CoreAdjPairFinset K).card + (CoreOldTwoStepPairFinset H).card := Finset.card_union_le _ _
  omega

lemma coreClosePair_card_le_host_raw {d m : ℕ} {P : Type} [Fintype P]
    {H : SimpleGraph (Fin m)} {root : P → Fin m} {K : SimpleGraph (Fin m ⊕ P)}
    (hHost : HostGraph d m H)
    (hGK : PendantCoreGraphSum H root ≤ K) (hKtf : K.CliqueFree 3) :
    (CoreClosePairFinset K).card ≤
      (m * d + (AddedEdgeFinset (PendantCoreGraphSum H root) K).card) +
        m * d * d +
          2 * (AddedEdgeFinset (PendantCoreGraphSum H root) K).card * H.indepNum := by
  classical
  have hclose := coreClosePair_card_le_adj_old_charged (H := H) (root := root) (K := K)
  have hadj := coreAdjPair_card_le_host_edges_add_added (H := H) (root := root) (K := K)
  have hedge := HostGraph.edgeSet_nat_card_le_card_mul hHost
  have hold :=
    coreOldTwoStepPair_card_le_card_mul_sq (m := m) (d := d) (H := H)
      hHost.maxDegreeAtMost
  have hcharged := coreChargedPair_card_le_two_mul_added_mul_indepNum (H := H) (root := root)
    (K := K) hGK hKtf
  omega

lemma coreClosePair_card_le_host {d m : ℕ} {P : Type} [Fintype P]
    {H : SimpleGraph (Fin m)} {root : P → Fin m} {K : SimpleGraph (Fin m ⊕ P)}
    (hHost : HostGraph d m H)
    (hGK : PendantCoreGraphSum H root ≤ K) (hKtf : K.CliqueFree 3) :
    (CoreClosePairFinset K).card ≤
      m * d + m * d * d +
        (AddedEdgeFinset (PendantCoreGraphSum H root) K).card * (1 + 2 * H.indepNum) := by
  have hraw := coreClosePair_card_le_host_raw (d := d) (m := m) (H := H) (root := root)
    (K := K) hHost hGK hKtf
  nlinarith [hraw]


lemma coreClosePair_card_real_le_host {d m : ℕ} {P : Type} [Fintype P]
    {H : SimpleGraph (Fin m)} {root : P → Fin m} {K : SimpleGraph (Fin m ⊕ P)}
    (hHost : HostGraph d m H)
    (hGK : PendantCoreGraphSum H root ≤ K) (hKtf : K.CliqueFree 3) :
    ((CoreClosePairFinset K).card : ℝ) ≤
      (m : ℝ) * (d : ℝ) + (m : ℝ) * (d : ℝ) * (d : ℝ) +
        ((AddedEdgeFinset (PendantCoreGraphSum H root) K).card : ℝ) *
          (1 + 2 * (H.indepNum : ℝ)) := by
  have hnat := coreClosePair_card_le_host (d := d) (m := m) (H := H) (root := root)
    (K := K) hHost hGK hKtf
  exact_mod_cast hnat

lemma coreClosePair_card_real_le_host_log {d m : ℕ} {P : Type} [Fintype P]
    {H : SimpleGraph (Fin m)} {root : P → Fin m} {K : SimpleGraph (Fin m ⊕ P)}
    (hHost : HostGraph d m H)
    (hGK : PendantCoreGraphSum H root ≤ K) (hKtf : K.CliqueFree 3) :
    ((CoreClosePairFinset K).card : ℝ) ≤
      (m : ℝ) * (d : ℝ) + (m : ℝ) * (d : ℝ) * (d : ℝ) +
        ((AddedEdgeFinset (PendantCoreGraphSum H root) K).card : ℝ) *
          (1 + 2 * (hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ))) := by
  have hbase := coreClosePair_card_real_le_host (d := d) (m := m) (H := H) (root := root)
    (K := K) hHost hGK hKtf
  have hfac : 1 + 2 * (H.indepNum : ℝ) ≤
      1 + 2 * (hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ)) := by
    nlinarith [HostGraph.indepNum_le hHost]
  have hmul := mul_le_mul_of_nonneg_left hfac
    (show 0 ≤ ((AddedEdgeFinset (PendantCoreGraphSum H root) K).card : ℝ) by positivity)
  nlinarith

lemma sym2_map_mem_edgeSet_comap_iff {V W : Type} (e : V ≃ W)
    (G : SimpleGraph W) (x : Sym2 V) :
    x.map e ∈ G.edgeSet ↔ x ∈ (G.comap e).edgeSet := by
  refine Sym2.ind ?_ x
  intro a b
  simp [SimpleGraph.mem_edgeSet]

noncomputable def sym2EquivOfEquiv {V W : Type} (e : V ≃ W) : Sym2 V ≃ Sym2 W where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv := by
    intro x
    rw [Sym2.map_map]
    refine Sym2.ind ?_ x
    intro a b
    simp [Sym2.map_pair_eq]
  right_inv := by
    intro x
    rw [Sym2.map_map]
    refine Sym2.ind ?_ x
    intro a b
    simp [Sym2.map_pair_eq]

@[simp] lemma sym2EquivOfEquiv_apply {V W : Type} (e : V ≃ W) (x : Sym2 V) :
    sym2EquivOfEquiv e x = x.map e := rfl

@[simp] lemma sym2EquivOfEquiv_symm_apply {V W : Type} (e : V ≃ W) (x : Sym2 W) :
    (sym2EquivOfEquiv e).symm x = x.map e.symm := rfl

lemma addedEdgeFinset_map_sym2Equiv_comap {V W : Type} [Fintype V] [Fintype W]
    (e : V ≃ W) (G K : SimpleGraph W) :
    (AddedEdgeFinset (G.comap e) (K.comap e)).map (sym2EquivOfEquiv e).toEmbedding =
      AddedEdgeFinset G K := by
  classical
  ext z
  constructor
  · intro hz
    rcases Finset.mem_map.mp hz with ⟨x, hx, hxz⟩
    rw [mem_addedEdgeFinset] at hx ⊢
    rw [← hxz]
    exact ⟨(sym2_map_mem_edgeSet_comap_iff e K x).2 hx.1,
      fun hG => hx.2 ((sym2_map_mem_edgeSet_comap_iff e G x).1 hG)⟩
  · intro hz
    rw [mem_addedEdgeFinset] at hz
    refine Finset.mem_map.mpr ⟨z.map e.symm, ?_, ?_⟩
    · rw [mem_addedEdgeFinset]
      have hKpre : z.map e.symm ∈ (K.comap e).edgeSet := by
        rw [← sym2_map_mem_edgeSet_comap_iff e K (z.map e.symm)]
        simpa [Sym2.map_map] using hz.1
      have hGpre : z.map e.symm ∉ (G.comap e).edgeSet := by
        intro hG
        apply hz.2
        have hGmap := (sym2_map_mem_edgeSet_comap_iff e G (z.map e.symm)).2 hG
        simpa [Sym2.map_map] using hGmap
      exact ⟨hKpre, hGpre⟩
    · simp [sym2EquivOfEquiv, Sym2.map_map]

lemma addedEdgeFinset_card_comap_equiv {V W : Type} [Fintype V] [Fintype W]
    (e : V ≃ W) (G K : SimpleGraph W) :
    (AddedEdgeFinset (G.comap e) (K.comap e)).card = (AddedEdgeFinset G K).card := by
  classical
  rw [← addedEdgeFinset_map_sym2Equiv_comap e G K, Finset.card_map]

lemma ediam_comap_equiv_le {V W : Type} (e : V ≃ W) {G : SimpleGraph W} {r : ℕ}
    (h : G.ediam ≤ (r : ℕ∞)) : (G.comap e).ediam ≤ (r : ℕ∞) := by
  apply ediam_le_of_forall_exists_walk_le
  intro u v
  have hed : G.edist (e u) (e v) ≤ (r : ℕ∞) :=
    (SimpleGraph.ediam_le_iff.mp h) (e u) (e v)
  rcases exists_walk_length_le_of_edist_le hed with ⟨p, hp⟩
  let iso := SimpleGraph.Iso.comap e G
  have hu : iso.symm (e u) = u := by
    change e.symm (e u) = u
    simp
  have hv : iso.symm (e v) = v := by
    change e.symm (e v) = v
    simp
  rw [← hu, ← hv]
  exact ⟨p.map iso.symm.toHom, by simpa [Walk.length_map] using hp⟩

lemma overFin_comap_equiv_eq {V : Type} [Fintype V] {n : ℕ} (G : SimpleGraph V)
    (hc : Fintype.card V = n) :
    (G.overFin hc).comap (Fintype.equivFinOfCardEq hc) = G := by
  ext u v
  simp [SimpleGraph.overFin]

lemma overFin_le_comap_of_le {V : Type} [Fintype V] {n : ℕ}
    {G : SimpleGraph V} {K : SimpleGraph (Fin n)} (hc : Fintype.card V = n)
    (hGK : G.overFin hc ≤ K) :
    G ≤ K.comap (Fintype.equivFinOfCardEq hc) := by
  classical
  let e := Fintype.equivFinOfCardEq hc
  intro u v huv
  have hfin : (G.overFin hc).Adj (e u) (e v) := by
    simpa [e, SimpleGraph.overFin] using huv
  exact hGK hfin

lemma cliqueFree_comap_equiv {V W : Type} (e : V ≃ W) {G : SimpleGraph W} {r : ℕ}
    (h : G.CliqueFree r) : (G.comap e).CliqueFree r := by
  exact SimpleGraph.CliqueFree.comap (SimpleGraph.Iso.comap e G).toEmbedding h

lemma addedEdgeCount_overFin_eq_addedEdgeFinset_comap {V : Type} [Fintype V] {n : ℕ}
    (G : SimpleGraph V) (K : SimpleGraph (Fin n)) (hc : Fintype.card V = n) :
    addedEdgeCount (G.overFin hc) K =
      (AddedEdgeFinset G (K.comap (Fintype.equivFinOfCardEq hc))).card := by
  classical
  let e := Fintype.equivFinOfCardEq hc
  have hG : (G.overFin hc).comap e = G := by
    simpa [e] using overFin_comap_equiv_eq G hc
  calc
    addedEdgeCount (G.overFin hc) K = (AddedEdgeFinset (G.overFin hc) K).card := by
      rw [addedEdgeCount_eq_addedEdgeFinset]
    _ = (AddedEdgeFinset ((G.overFin hc).comap e) (K.comap e)).card := by
      exact (addedEdgeFinset_card_comap_equiv e (G.overFin hc) K).symm
    _ = (AddedEdgeFinset G (K.comap e)).card := by
      rw [hG]

/-- The finite set of pendant-pair components with no new edge to the core. -/
def CoreFreeComponentFinset {C P : Type} [Fintype P]
    (K : SimpleGraph (C ⊕ P)) (root : P → C) :
    Finset (PendantPairGraph K).ConnectedComponent := by
  classical
  exact Finset.univ.filter fun X => PendantComponentCoreFree K root X

@[simp] lemma mem_coreFreeComponentFinset {C P : Type} [Fintype P]
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X : (PendantPairGraph K).ConnectedComponent} :
    X ∈ CoreFreeComponentFinset K root ↔ PendantComponentCoreFree K root X := by
  classical
  simp [CoreFreeComponentFinset]

/-- The finite set of pendant-pair components that have a new edge to the core. -/
def CoreTouchingComponentFinset {C P : Type} [Fintype P]
    (K : SimpleGraph (C ⊕ P)) (root : P → C) :
    Finset (PendantPairGraph K).ConnectedComponent := by
  classical
  exact Finset.univ.filter fun X => PendantComponentCoreTouching K root X

@[simp] lemma mem_coreTouchingComponentFinset {C P : Type} [Fintype P]
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X : (PendantPairGraph K).ConnectedComponent} :
    X ∈ CoreTouchingComponentFinset K root ↔ PendantComponentCoreTouching K root X := by
  classical
  simp [CoreTouchingComponentFinset]

/-- A chosen new pendant-core edge witnessing that a component is core-touching. -/
noncomputable def touchingComponentWitness {C P : Type} [Fintype P]
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    (X : {X : (PendantPairGraph K).ConnectedComponent //
      X ∈ CoreTouchingComponentFinset K root}) :
    {pc : P × C //
      pc.1 ∈ X.1.supp ∧ K.Adj (Sum.inr pc.1) (Sum.inl pc.2) ∧ pc.2 ≠ root pc.1} := by
  classical
  have htouch : PendantComponentCoreTouching K root X.1 :=
    (mem_coreTouchingComponentFinset (K := K) (root := root)).mp X.2
  let h := not_coreFree_iff_exists_new_core_edge.mp htouch
  let p : P := Classical.choose h
  have hp_spec : p ∈ X.1.supp ∧
      ∃ c : C, K.Adj (Sum.inr p) (Sum.inl c) ∧ c ≠ root p := Classical.choose_spec h
  let hc_exists := hp_spec.2
  let c : C := Classical.choose hc_exists
  have hc_spec : K.Adj (Sum.inr p) (Sum.inl c) ∧ c ≠ root p :=
    Classical.choose_spec hc_exists
  exact ⟨(p, c), hp_spec.1, hc_spec.1, hc_spec.2⟩

lemma sym2_inr_inr_ne_inr_inl {C P : Type} {p q r : P} {c : C} :
    s((Sum.inr p : C ⊕ P), Sum.inr q) ≠ s(Sum.inr r, Sum.inl c) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨_, hbad⟩ | ⟨hbad, _⟩ <;> cases hbad

lemma sym2Map_inr_ne_inr_inl {C P : Type} {e : Sym2 P} {p : P} {c : C} :
    ((Function.Embedding.inr : P ↪ C ⊕ P).sym2Map e) ≠
      s((Sum.inr p : C ⊕ P), Sum.inl c) := by
  intro h
  refine Sym2.ind ?_ e h
  intro a b hab
  have hshape : s((Sum.inr a : C ⊕ P), Sum.inr b) = s((Sum.inr p : C ⊕ P), Sum.inl c) := by
    simp [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq] at hab
  exact sym2_inr_inr_ne_inr_inl hshape

lemma sym2_inr_inl_eq_inr_inl {C P : Type} {p q : P} {a b : C}
    (h : s((Sum.inr p : C ⊕ P), Sum.inl a) = s(Sum.inr q, Sum.inl b)) :
    p = q ∧ a = b := by
  rw [Sym2.eq_iff] at h
  rcases h with ⟨hp, ha⟩ | ⟨hbad, _⟩
  · exact ⟨Sum.inr.inj hp, Sum.inl.inj ha⟩
  · cases hbad

lemma pendantPair_edges_add_touchingComponents_le_addedEdgeFinset {C P : Type}
    [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)} :
    Nat.card (PendantPairGraph K).edgeSet + (CoreTouchingComponentFinset K root).card ≤
      (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
  classical
  let touch := CoreTouchingComponentFinset K root
  let pinr : P ↪ C ⊕ P := Function.Embedding.inr
  let charge :
      (PendantPairGraph K).edgeSet ⊕
          {X : (PendantPairGraph K).ConnectedComponent // X ∈ touch} →
        {e : Sym2 (C ⊕ P) // e ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K}
    | Sum.inl e =>
        ⟨pinr.sym2Map e.1, by
          refine Sym2.ind ?_ e.1 e.2
          intro p q hpq
          have hpq' : K.Adj (Sum.inr p) (Sum.inr q) := by
            simpa [SimpleGraph.mem_edgeSet] using hpq
          simp [pinr, mem_addedEdgeFinset, Function.Embedding.sym2Map_apply, Sym2.map_pair_eq,
            hpq']⟩
    | Sum.inr X =>
        let w := touchingComponentWitness (K := K) (root := root) X
        ⟨s((Sum.inr w.1.1 : C ⊕ P), Sum.inl w.1.2), by
          have hK : K.Adj (Sum.inr w.1.1) (Sum.inl w.1.2) := w.2.2.1
          have hnew : w.1.2 ≠ root w.1.1 := w.2.2.2
          rw [mem_addedEdgeFinset]
          refine ⟨?_, ?_⟩
          · simpa [SimpleGraph.mem_edgeSet] using hK
          · intro hbase
            have hroot : w.1.2 = root w.1.1 := by
              simpa [SimpleGraph.mem_edgeSet] using hbase
            exact hnew hroot⟩
  have hcharge : Function.Injective charge := by
    intro x y hxy
    cases x with
    | inl e =>
        cases y with
        | inl e' =>
            apply congrArg Sum.inl
            apply Subtype.ext
            have hval : pinr.sym2Map e.1 = pinr.sym2Map e'.1 := by
              simpa [charge] using congrArg Subtype.val hxy
            exact pinr.sym2Map.injective hval
        | inr X =>
            exfalso
            let w := touchingComponentWitness (K := K) (root := root) X
            have hval : pinr.sym2Map e.1 = s((Sum.inr w.1.1 : C ⊕ P), Sum.inl w.1.2) := by
              simpa [charge, w] using congrArg Subtype.val hxy
            exact sym2Map_inr_ne_inr_inl (C := C) (P := P) hval
    | inr X =>
        cases y with
        | inl e =>
            exfalso
            let w := touchingComponentWitness (K := K) (root := root) X
            have hval : s((Sum.inr w.1.1 : C ⊕ P), Sum.inl w.1.2) = pinr.sym2Map e.1 := by
              simpa [charge, w] using congrArg Subtype.val hxy
            exact sym2Map_inr_ne_inr_inl (C := C) (P := P) hval.symm
        | inr Y =>
            apply congrArg Sum.inr
            apply Subtype.ext
            let wx := touchingComponentWitness (K := K) (root := root) X
            let wy := touchingComponentWitness (K := K) (root := root) Y
            have hval : s((Sum.inr wx.1.1 : C ⊕ P), Sum.inl wx.1.2) =
                s((Sum.inr wy.1.1 : C ⊕ P), Sum.inl wy.1.2) := by
              simpa [charge, wx, wy] using congrArg Subtype.val hxy
            have hp : wx.1.1 = wy.1.1 := (sym2_inr_inl_eq_inr_inl hval).1
            exact SimpleGraph.ConnectedComponent.eq_of_common_vertex
              (by simpa [hp] using wx.2.1) wy.2.1
  have hcard := Nat.card_le_card_of_injective charge hcharge
  have htouchCard : Nat.card {X : (PendantPairGraph K).ConnectedComponent // X ∈ touch} =
      touch.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have hcod : Nat.card
      {e : Sym2 (C ⊕ P) // e ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K} =
      (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Nat.card_sum, htouchCard, hcod] at hcard
  simpa [touch] using hcard

lemma coreFreeComponent_card_add_touchingComponent_card {C P : Type} [Fintype P]
    {K : SimpleGraph (C ⊕ P)} {root : P → C} :
    (CoreFreeComponentFinset K root).card + (CoreTouchingComponentFinset K root).card =
      Nat.card (PendantPairGraph K).ConnectedComponent := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp [CoreFreeComponentFinset, CoreTouchingComponentFinset, PendantComponentCoreTouching,
    Finset.card_filter_add_card_filter_not]

/-- Core-free pendant-pair components containing a pendant with a specified root. -/
def CoreFreeComponentsAtRootFinset {C P : Type} [Fintype P]
    (K : SimpleGraph (C ⊕ P)) (root : P → C) (c : C) :
    Finset (PendantPairGraph K).ConnectedComponent := by
  classical
  exact (CoreFreeComponentFinset K root).filter fun X => ∃ p : P, p ∈ X.supp ∧ root p = c

@[simp] lemma mem_coreFreeComponentsAtRootFinset {C P : Type} [Fintype P]
    {K : SimpleGraph (C ⊕ P)} {root : P → C} {c : C}
    {X : (PendantPairGraph K).ConnectedComponent} :
    X ∈ CoreFreeComponentsAtRootFinset K root c ↔
      PendantComponentCoreFree K root X ∧ ∃ p : P, p ∈ X.supp ∧ root p = c := by
  classical
  simp [CoreFreeComponentsAtRootFinset]

noncomputable def coreFreeComponentAtRootWitness {C P : Type} [Fintype P]
    {K : SimpleGraph (C ⊕ P)} {root : P → C} {c : C}
    (X : {X : (PendantPairGraph K).ConnectedComponent //
      X ∈ CoreFreeComponentsAtRootFinset K root c}) :
    {p : P // p ∈ X.1.supp ∧ root p = c} := by
  classical
  have hx : ∃ p : P, p ∈ X.1.supp ∧ root p = c :=
    (mem_coreFreeComponentsAtRootFinset (K := K) (root := root) (c := c)).mp X.2 |>.2
  let p : P := Classical.choose hx
  exact ⟨p, Classical.choose_spec hx⟩

lemma coreFreeComponentsAtRoot_card_le_rootFiber {C P : Type} [Fintype P]
    {K : SimpleGraph (C ⊕ P)} {root : P → C} (c : C) :
    (CoreFreeComponentsAtRootFinset K root c).card ≤ Nat.card {p : P // root p = c} := by
  classical
  let A := CoreFreeComponentsAtRootFinset K root c
  let f : {X : (PendantPairGraph K).ConnectedComponent // X ∈ A} → {p : P // root p = c} :=
    fun X =>
      let w := coreFreeComponentAtRootWitness (K := K) (root := root) (c := c) X
      ⟨w.1, w.2.2⟩
  have hf : Function.Injective f := by
    intro X Y hXY
    apply Subtype.ext
    let wx := coreFreeComponentAtRootWitness (K := K) (root := root) (c := c) X
    let wy := coreFreeComponentAtRootWitness (K := K) (root := root) (c := c) Y
    have hp : wx.1 = wy.1 := by
      simpa [f, wx, wy] using congrArg Subtype.val hXY
    exact SimpleGraph.ConnectedComponent.eq_of_common_vertex
      (by simpa [hp] using wx.2.1) wy.2.1
  have hcard := Nat.card_le_card_of_injective f hf
  have hA : Nat.card {X : (PendantPairGraph K).ConnectedComponent // X ∈ A} = A.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact le_of_eq_of_le hA.symm hcard

lemma coreFreeComponent_card_le_sum_roots {C P : Type} [Fintype C] [Fintype P]
    {K : SimpleGraph (C ⊕ P)} {root : P → C} :
    (CoreFreeComponentFinset K root).card ≤
      ∑ c : C, (CoreFreeComponentsAtRootFinset K root c).card := by
  classical
  let free := CoreFreeComponentFinset K root
  let atRoot := fun c : C => CoreFreeComponentsAtRootFinset K root c
  have hsubset : free ⊆ Finset.univ.biUnion atRoot := by
    intro X hX
    rcases X.nonempty_supp with ⟨p, hp⟩
    have hXfree : PendantComponentCoreFree K root X := by simpa [free] using hX
    have hXat : X ∈ atRoot (root p) := by
      simpa [atRoot] using ⟨hXfree, p, hp, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨root p, by simp, hXat⟩
  calc
    free.card ≤ (Finset.univ.biUnion atRoot).card := Finset.card_le_card hsubset
    _ ≤ ∑ c ∈ (Finset.univ : Finset C), (atRoot c).card := Finset.card_biUnion_le
    _ = ∑ c : C, (CoreFreeComponentsAtRootFinset K root c).card := by simp [atRoot]


/-- Ordered pairs of distinct core-free components are controlled by same-root collisions and close
ordered root pairs.  This is the finite combinatorial core of Lemma 3. -/
lemma coreFreeComponent_offDiag_card_le_root_close {C P : Type} [Fintype C] [Fintype P]
    {K : SimpleGraph (C ⊕ P)} {root : P → C} {S : ℕ}
    (hKdiam : K.ediam ≤ (4 : ℕ∞))
    (hS : ∀ c : C, (CoreFreeComponentsAtRootFinset K root c).card ≤ S) :
    ((CoreFreeComponentFinset K root).offDiag).card ≤
      Fintype.card C * S * S + 2 * (CoreClosePairFinset K).card * S * S := by
  classical
  let free := CoreFreeComponentFinset K root
  let atRoot := fun c : C => CoreFreeComponentsAtRootFinset K root c
  let samePairs : Finset ((PendantPairGraph K).ConnectedComponent ×
      (PendantPairGraph K).ConnectedComponent) :=
    (Finset.univ : Finset C).biUnion fun c => (atRoot c).product (atRoot c)
  let closePairs : Finset ((PendantPairGraph K).ConnectedComponent ×
      (PendantPairGraph K).ConnectedComponent) :=
    (CoreCloseOrderedPairFinset K).biUnion fun ab => (atRoot ab.1).product (atRoot ab.2)
  have hsubset : free.offDiag ⊆ samePairs ∪ closePairs := by
    intro XY hXY
    rcases (Finset.mem_offDiag.mp hXY) with ⟨hXfree_mem, hYfree_mem, hXYne⟩
    have hXfree : PendantComponentCoreFree K root XY.1 := by simpa [free] using hXfree_mem
    have hYfree : PendantComponentCoreFree K root XY.2 := by simpa [free] using hYfree_mem
    rcases coreFree_components_exists_coreClose_of_ediam_le_four
        (K := K) (root := root) hKdiam hXfree hYfree hXYne with
      ⟨u, huX, v, hvY, hclose⟩
    have hXat : XY.1 ∈ atRoot (root u) := by
      exact (mem_coreFreeComponentsAtRootFinset (K := K) (root := root) (c := root u)).mpr
        ⟨hXfree, u, huX, rfl⟩
    by_cases hroot : root u = root v
    · have hYat : XY.2 ∈ atRoot (root u) := by
        exact (mem_coreFreeComponentsAtRootFinset (K := K) (root := root) (c := root u)).mpr
          ⟨hYfree, v, hvY, hroot.symm⟩
      apply Finset.mem_union.mpr
      left
      change XY ∈ (Finset.univ : Finset C).biUnion fun c => (atRoot c).product (atRoot c)
      apply Finset.mem_biUnion.mpr
      refine ⟨root u, by simp, ?_⟩
      exact Finset.mem_product.mpr ⟨hXat, hYat⟩
    · have hYat : XY.2 ∈ atRoot (root v) := by
        exact (mem_coreFreeComponentsAtRootFinset (K := K) (root := root) (c := root v)).mpr
          ⟨hYfree, v, hvY, rfl⟩
      have hordered : (root u, root v) ∈ CoreCloseOrderedPairFinset K := by
        exact (mem_coreCloseOrderedPairFinset (K := K)).mpr
          ⟨hroot, (mem_coreClosePairFinset_mk (K := K)).mpr ⟨hroot, hclose⟩⟩
      apply Finset.mem_union.mpr
      right
      change XY ∈ (CoreCloseOrderedPairFinset K).biUnion fun ab =>
        (atRoot ab.1).product (atRoot ab.2)
      apply Finset.mem_biUnion.mpr
      refine ⟨(root u, root v), hordered, ?_⟩
      exact Finset.mem_product.mpr ⟨hXat, hYat⟩
  have hpairCard : free.offDiag.card ≤ samePairs.card + closePairs.card := by
    exact (Finset.card_le_card hsubset).trans (Finset.card_union_le samePairs closePairs)
  have hsameCard : samePairs.card ≤ ∑ c : C, (atRoot c).card * (atRoot c).card := by
    calc
      samePairs.card ≤ ∑ c ∈ (Finset.univ : Finset C), ((atRoot c).product (atRoot c)).card := by
        simpa [samePairs] using
          (Finset.card_biUnion_le (s := (Finset.univ : Finset C))
            (t := fun c : C => (atRoot c).product (atRoot c)))
      _ = ∑ c : C, (atRoot c).card * (atRoot c).card := by
        simp [Finset.card_product]
  have hsameBound : samePairs.card ≤ Fintype.card C * S * S := by
    calc
      samePairs.card ≤ ∑ c : C, (atRoot c).card * (atRoot c).card := hsameCard
      _ ≤ ∑ _c : C, S * S := by
        refine Finset.sum_le_sum ?_
        intro c _
        exact Nat.mul_le_mul (hS c) (hS c)
      _ = Fintype.card C * S * S := by
        simp [Nat.mul_assoc]
  have hcloseCard : closePairs.card ≤
      ∑ ab ∈ CoreCloseOrderedPairFinset K, (atRoot ab.1).card * (atRoot ab.2).card := by
    calc
      closePairs.card ≤
          ∑ ab ∈ CoreCloseOrderedPairFinset K, ((atRoot ab.1).product (atRoot ab.2)).card := by
        simpa [closePairs] using
          (Finset.card_biUnion_le (s := CoreCloseOrderedPairFinset K)
            (t := fun ab : C × C => (atRoot ab.1).product (atRoot ab.2)))
      _ = ∑ ab ∈ CoreCloseOrderedPairFinset K, (atRoot ab.1).card * (atRoot ab.2).card := by
        simp [Finset.card_product]
  have hcloseBound : closePairs.card ≤ 2 * (CoreClosePairFinset K).card * S * S := by
    calc
      closePairs.card ≤
          ∑ ab ∈ CoreCloseOrderedPairFinset K, (atRoot ab.1).card * (atRoot ab.2).card := hcloseCard
      _ ≤ ∑ _ab ∈ CoreCloseOrderedPairFinset K, S * S := by
        refine Finset.sum_le_sum ?_
        intro ab _
        exact Nat.mul_le_mul (hS ab.1) (hS ab.2)
      _ = (CoreCloseOrderedPairFinset K).card * (S * S) := by simp [Finset.sum_const]
      _ ≤ (2 * (CoreClosePairFinset K).card) * (S * S) := by
        exact Nat.mul_le_mul_right (S * S) (coreCloseOrderedPair_card_le_two_mul (K := K))
      _ = 2 * (CoreClosePairFinset K).card * S * S := by ring
  exact hpairCard.trans (Nat.add_le_add hsameBound hcloseBound)

lemma pendant_component_accounting {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)} :
    Nat.card P - (CoreFreeComponentFinset K root).card ≤
      (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
  classical
  let F : SimpleGraph P := PendantPairGraph K
  let free := CoreFreeComponentFinset K root
  let touch := CoreTouchingComponentFinset K root
  have hvertices : Nat.card P ≤ Nat.card F.edgeSet + Nat.card F.ConnectedComponent :=
    card_vertex_le_edgeSet_add_connectedComponents F
  have hcomponents : free.card + touch.card = Nat.card F.ConnectedComponent := by
    simpa [F, free, touch] using
      (coreFreeComponent_card_add_touchingComponent_card (K := K) (root := root))
  have hcharge : Nat.card F.edgeSet + touch.card ≤
      (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
    simpa [F, touch] using
      (pendantPair_edges_add_touchingComponents_le_addedEdgeFinset (H := H) (root := root) (K := K))
  have hmid : Nat.card P - free.card ≤ Nat.card F.edgeSet + touch.card := by
    omega
  exact hmid.trans hcharge

lemma pendantPair_edgeSet_card_le_addedEdgeFinset {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)} :
    Nat.card (PendantPairGraph K).edgeSet ≤
      (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
  classical
  let pinr : P ↪ C ⊕ P := Function.Embedding.inr
  let f : (PendantPairGraph K).edgeSet →
      {e : Sym2 (C ⊕ P) // e ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K} := fun e =>
    ⟨pinr.sym2Map e.1, by
      refine Sym2.ind ?_ e.1 e.2
      intro p q hpq
      have hpq' : K.Adj (Sum.inr p) (Sum.inr q) := by
        simpa [SimpleGraph.mem_edgeSet] using hpq
      simp [pinr, mem_addedEdgeFinset, Function.Embedding.sym2Map_apply, Sym2.map_pair_eq, hpq']⟩
  have hf : Function.Injective f := by
    intro e₁ e₂ h
    apply Subtype.ext
    have hval : pinr.sym2Map e₁.1 = pinr.sym2Map e₂.1 := by
      simpa [f] using congrArg Subtype.val h
    exact pinr.sym2Map.injective hval
  have hcard := Nat.card_le_card_of_injective f hf
  have hcod : Nat.card
      {e : Sym2 (C ⊕ P) // e ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K} =
      (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hcod] at hcard
  exact hcard

/-- The explicit hub supergraph used only to show that the feasible set in `IsHR` is nonempty.
It adds a star from one chosen pendant `hub` to every pendant over a different root. -/
def PendantHubSupergraphSum {C P : Type} (H : SimpleGraph C) (root : P → C) (hub : P) :
    SimpleGraph (C ⊕ P) where
  Adj x y :=
    (PendantCoreGraphSum H root).Adj x y ∨
      ∃ p : P, root p ≠ root hub ∧
        ((x = Sum.inr hub ∧ y = Sum.inr p) ∨ (x = Sum.inr p ∧ y = Sum.inr hub))
  symm := by
    intro x y h
    rcases h with hbase | ⟨p, hp, hnew⟩
    · exact Or.inl hbase.symm
    · rcases hnew with ⟨hxhub, hyp⟩ | ⟨hxp, hyhub⟩
      · exact Or.inr ⟨p, hp, Or.inr ⟨hyp, hxhub⟩⟩
      · exact Or.inr ⟨p, hp, Or.inl ⟨hyhub, hxp⟩⟩
  loopless := by
    intro x h
    rcases h with hbase | ⟨p, hp, hnew⟩
    · exact (PendantCoreGraphSum H root).irrefl hbase
    · rcases hnew with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · have : p = hub := by simpa using h₂.symm.trans h₁
        exact hp (by rw [this])
      · have : p = hub := by simpa using h₁.symm.trans h₂
        exact hp (by rw [this])

lemma pendantCoreGraphSum_le_hubSupergraph {C P : Type} (H : SimpleGraph C) (root : P → C)
    (hub : P) :
    PendantCoreGraphSum H root ≤ PendantHubSupergraphSum H root hub := by
  intro x y hxy
  exact Or.inl hxy

@[simp] lemma pendantHubSupergraphSum_adj_core_core {C P : Type} {H : SimpleGraph C}
    {root : P → C} {hub : P} {a b : C} :
    (PendantHubSupergraphSum H root hub).Adj (Sum.inl a) (Sum.inl b) ↔ H.Adj a b := by
  constructor
  · intro h
    rcases h with hbase | ⟨p, hp, hnew⟩
    · exact hbase
    · rcases hnew with ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> cases h₁
  · intro h
    exact Or.inl h

@[simp] lemma pendantHubSupergraphSum_adj_hub_pendant {C P : Type} {H : SimpleGraph C}
    {root : P → C} {hub p : P} (hp : root p ≠ root hub) :
    (PendantHubSupergraphSum H root hub).Adj (Sum.inr hub) (Sum.inr p) := by
  exact Or.inr ⟨p, hp, Or.inl ⟨rfl, rfl⟩⟩

@[simp] lemma pendantHubSupergraphSum_adj_core_pendant {C P : Type} {H : SimpleGraph C}
    {root : P → C} {hub : P} {a : C} {p : P} :
    (PendantHubSupergraphSum H root hub).Adj (Sum.inl a) (Sum.inr p) ↔ root p = a := by
  constructor
  · intro h
    rcases h with hbase | ⟨q, _, hnew⟩
    · exact hbase.symm
    · rcases hnew with ⟨hcore, _⟩ | ⟨hcore, _⟩ <;> cases hcore
  · intro h
    exact Or.inl (by simpa [eq_comm] using h)

@[simp] lemma pendantHubSupergraphSum_adj_pendant_core {C P : Type} {H : SimpleGraph C}
    {root : P → C} {hub : P} {p : P} {a : C} :
    (PendantHubSupergraphSum H root hub).Adj (Sum.inr p) (Sum.inl a) ↔ root p = a := by
  rw [adj_comm, pendantHubSupergraphSum_adj_core_pendant]

@[simp] lemma pendantHubSupergraphSum_adj_pendant_pendant {C P : Type} {H : SimpleGraph C}
    {root : P → C} {hub p q : P} :
    (PendantHubSupergraphSum H root hub).Adj (Sum.inr p) (Sum.inr q) ↔
      (p = hub ∧ root q ≠ root hub) ∨ (q = hub ∧ root p ≠ root hub) := by
  constructor
  · intro h
    rcases h with hbase | ⟨r, hr, hnew⟩
    · exact False.elim hbase
    · rcases hnew with ⟨hp, hq⟩ | ⟨hp, hq⟩
      · left
        refine ⟨?_, ?_⟩
        · simpa using hp
        · have hqr : q = r := by simpa using hq
          simpa [hqr] using hr
      · right
        refine ⟨?_, ?_⟩
        · simpa using hq
        · have hpr : p = r := by simpa using hp
          simpa [hpr] using hr
  · intro h
    rcases h with ⟨hp, hqroot⟩ | ⟨hq, hproot⟩
    · subst p
      exact Or.inr ⟨q, hqroot, Or.inl ⟨rfl, rfl⟩⟩
    · subst q
      exact Or.inr ⟨p, hproot, Or.inr ⟨rfl, rfl⟩⟩

lemma pendantHubSupergraphSum_walk_to_hub_le_two {C P : Type} (H : SimpleGraph C)
    (root : P → C) (hub : P)
    (hcover : ∀ c : C, c ≠ root hub → ∃ p : P, root p = c) :
    ∀ x : C ⊕ P, ∃ p : (PendantHubSupergraphSum H root hub).Walk x (Sum.inr hub),
      p.length ≤ 2 := by
  intro x
  cases x with
  | inl a =>
      by_cases ha : a = root hub
      · have hbase : (PendantHubSupergraphSum H root hub).Adj (Sum.inl a) (Sum.inr hub) := by
          exact Or.inl (by simp [ha])
        exact ⟨hbase.toWalk, by simp⟩
      · rcases hcover a ha with ⟨p, hp⟩
        have hbase : (PendantHubSupergraphSum H root hub).Adj (Sum.inl a) (Sum.inr p) := by
          exact Or.inl (by simp [hp])
        have hp_ne : root p ≠ root hub := by
          intro h
          exact ha (hp.symm.trans h)
        have hnew : (PendantHubSupergraphSum H root hub).Adj (Sum.inr p) (Sum.inr hub) := by
          exact Or.inr ⟨p, hp_ne, Or.inr ⟨rfl, rfl⟩⟩
        exact ⟨Walk.cons hbase hnew.toWalk, by simp⟩
  | inr p =>
      by_cases hp : root p = root hub
      · have hbase₁ : (PendantHubSupergraphSum H root hub).Adj
            (Sum.inr p) (Sum.inl (root p)) := by
          exact Or.inl (by simp)
        have hbase₂ : (PendantHubSupergraphSum H root hub).Adj
            (Sum.inl (root p)) (Sum.inr hub) := by
          exact Or.inl (by simp [hp])
        exact ⟨Walk.cons hbase₁ hbase₂.toWalk, by simp⟩
      · have hnew : (PendantHubSupergraphSum H root hub).Adj (Sum.inr p) (Sum.inr hub) := by
          exact Or.inr ⟨p, hp, Or.inr ⟨rfl, rfl⟩⟩
        exact ⟨hnew.toWalk, by simp⟩

lemma pendantHubSupergraphSum_walk_le_four {C P : Type} (H : SimpleGraph C)
    (root : P → C) (hub : P)
    (hcover : ∀ c : C, c ≠ root hub → ∃ p : P, root p = c) :
    ∀ x y : C ⊕ P, ∃ p : (PendantHubSupergraphSum H root hub).Walk x y,
      p.length ≤ 4 := by
  intro x y
  rcases pendantHubSupergraphSum_walk_to_hub_le_two H root hub hcover x with ⟨px, hpx⟩
  rcases pendantHubSupergraphSum_walk_to_hub_le_two H root hub hcover y with ⟨py, hpy⟩
  refine ⟨px.append py.reverse, ?_⟩
  rw [Walk.length_append, Walk.length_reverse]
  simpa using Nat.add_le_add hpx hpy

lemma pendantHubSupergraphSum_ediam_le_four {C P : Type} (H : SimpleGraph C)
    (root : P → C) (hub : P)
    (hcover : ∀ c : C, c ≠ root hub → ∃ p : P, root p = c) :
    (PendantHubSupergraphSum H root hub).ediam ≤ (4 : ℕ∞) := by
  apply ediam_le_of_forall_exists_walk_le
  intro x y
  rcases pendantHubSupergraphSum_walk_to_hub_le_two H root hub hcover x with ⟨px, hpx⟩
  rcases pendantHubSupergraphSum_walk_to_hub_le_two H root hub hcover y with ⟨py, hpy⟩
  refine ⟨px.append py.reverse, ?_⟩
  rw [Walk.length_append, Walk.length_reverse]
  simpa using Nat.add_le_add hpx hpy

/-- In a complete-graph embedding into a pendant-core graph, if one source vertex lands on a
pendant, every other source vertex lands on that pendant's root. -/
theorem embedding_eq_root_of_maps_to_pendant {C P : Type} {H : SimpleGraph C} {root : P → C}
    {k : ℕ} (f : completeGraph (Fin k) ↪g PendantCoreGraphSum H root)
    {i : Fin k} {p : P} (hi : f i = Sum.inr p) {j : Fin k} (hij : j ≠ i) :
    f j = Sum.inl (root p) := by
  have hadjSrc : (completeGraph (Fin k)).Adj i j := by simpa [top_adj] using hij.symm
  have hadj : (PendantCoreGraphSum H root).Adj (f i) (f j) :=
    (RelEmbedding.map_rel_iff f).2 hadjSrc
  rw [hi] at hadj
  exact pendantCoreGraphSum_adj_pendant_iff.mp hadj


/-- No embedding of a triangle into a pendant-core graph can send any source vertex to a pendant. -/
theorem not_exists_triangle_embedding_maps_to_pendant {C P : Type} {H : SimpleGraph C}
    {root : P → C}
    (f : completeGraph (Fin 3) ↪g PendantCoreGraphSum H root) :
    ¬ ∃ (i : Fin 3) (p : P), f i = Sum.inr p := by
  rintro ⟨i, p, hi⟩
  fin_cases i
  · have h1 := embedding_eq_root_of_maps_to_pendant f hi (j := (1 : Fin 3)) (by decide)
    have h2 := embedding_eq_root_of_maps_to_pendant f hi (j := (2 : Fin 3)) (by decide)
    have heq : f (1 : Fin 3) = f (2 : Fin 3) := h1.trans h2.symm
    exact (by decide : (1 : Fin 3) ≠ 2) (RelEmbedding.injective f heq)
  · have h0 := embedding_eq_root_of_maps_to_pendant f hi (j := (0 : Fin 3)) (by decide)
    have h2 := embedding_eq_root_of_maps_to_pendant f hi (j := (2 : Fin 3)) (by decide)
    have heq : f (0 : Fin 3) = f (2 : Fin 3) := h0.trans h2.symm
    exact (by decide : (0 : Fin 3) ≠ 2) (RelEmbedding.injective f heq)
  · have h0 := embedding_eq_root_of_maps_to_pendant f hi (j := (0 : Fin 3)) (by decide)
    have h1 := embedding_eq_root_of_maps_to_pendant f hi (j := (1 : Fin 3)) (by decide)
    have heq : f (0 : Fin 3) = f (1 : Fin 3) := h0.trans h1.symm
    exact (by decide : (0 : Fin 3) ≠ 1) (RelEmbedding.injective f heq)


/-- If a triangle embedding into a pendant-core graph uses no pendant vertices, it induces a
triangle embedding into the core. -/
theorem false_of_triangle_embedding_all_core {C P : Type} {H : SimpleGraph C} {root : P → C}
    (hH : H.CliqueFree 3)
    (f : completeGraph (Fin 3) ↪g PendantCoreGraphSum H root)
    (hno : ¬ ∃ (i : Fin 3) (p : P), f i = Sum.inr p) : False := by
  obtain ⟨c0, h0⟩ : ∃ c : C, f (0 : Fin 3) = Sum.inl c := by
    cases h : f (0 : Fin 3) with
    | inl c => exact ⟨c, rfl⟩
    | inr p => exact False.elim (hno ⟨0, p, h⟩)
  obtain ⟨c1, h1⟩ : ∃ c : C, f (1 : Fin 3) = Sum.inl c := by
    cases h : f (1 : Fin 3) with
    | inl c => exact ⟨c, rfl⟩
    | inr p => exact False.elim (hno ⟨1, p, h⟩)
  obtain ⟨c2, h2⟩ : ∃ c : C, f (2 : Fin 3) = Sum.inl c := by
    cases h : f (2 : Fin 3) with
    | inl c => exact ⟨c, rfl⟩
    | inr p => exact False.elim (hno ⟨2, p, h⟩)
  have h01 : H.Adj c0 c1 := by
    have hs : (completeGraph (Fin 3)).Adj (0 : Fin 3) 1 := by simp [top_adj]
    have ht := (RelEmbedding.map_rel_iff f).2 hs
    simpa [h0, h1] using ht
  have h02 : H.Adj c0 c2 := by
    have hs : (completeGraph (Fin 3)).Adj (0 : Fin 3) 2 := by simp [top_adj]
    have ht := (RelEmbedding.map_rel_iff f).2 hs
    simpa [h0, h2] using ht
  have h12 : H.Adj c1 c2 := by
    have hs : (completeGraph (Fin 3)).Adj (1 : Fin 3) 2 := by simp [top_adj]
    have ht := (RelEmbedding.map_rel_iff f).2 hs
    simpa [h1, h2] using ht
  have hc01 : c0 ≠ c1 := by
    intro hc
    apply (by decide : (0 : Fin 3) ≠ 1)
    apply RelEmbedding.injective f
    rw [h0, h1, hc]
  have hc02 : c0 ≠ c2 := by
    intro hc
    apply (by decide : (0 : Fin 3) ≠ 2)
    apply RelEmbedding.injective f
    rw [h0, h2, hc]
  have hc12 : c1 ≠ c2 := by
    intro hc
    apply (by decide : (1 : Fin 3) ≠ 2)
    apply RelEmbedding.injective f
    rw [h1, h2, hc]
  let g : Fin 3 → C := fun i =>
    match i with
    | 0 => c0
    | 1 => c1
    | 2 => c2
  have ginj : Function.Injective g := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [g] at hab ⊢
    · exact False.elim (hc01 hab)
    · exact False.elim (hc02 hab)
    · exact False.elim (hc01 hab.symm)
    · exact False.elim (hc12 hab)
    · exact False.elim (hc02 hab.symm)
    · exact False.elim (hc12 hab.symm)
  let emb : completeGraph (Fin 3) ↪g H :=
    { toEmbedding := ⟨g, ginj⟩
      map_rel_iff' := by
        intro a b
        constructor
        · intro hab
          have hne : a ≠ b := by
            intro heq
            subst b
            exact H.irrefl hab
          simpa [top_adj] using hne
        · intro hab
          fin_cases a <;> fin_cases b <;> simp [g, top_adj] at hab ⊢
          · exact h01
          · exact h02
          · exact h01.symm
          · exact h12
          · exact h02.symm
          · exact h12.symm }
  exact (SimpleGraph.cliqueFree_iff.mp hH).false emb

/-- Attaching pendant leaves to a triangle-free core preserves triangle-freeness. -/
theorem pendantCoreGraphSum_cliqueFree_three {C P : Type} {H : SimpleGraph C} {root : P → C}
    (hH : H.CliqueFree 3) : (PendantCoreGraphSum H root).CliqueFree 3 := by
  rw [SimpleGraph.cliqueFree_iff]
  refine ⟨?_⟩
  intro f
  by_cases hpend : ∃ (i : Fin 3) (p : P), f i = Sum.inr p
  · exact not_exists_triangle_embedding_maps_to_pendant f hpend
  · exact false_of_triangle_embedding_all_core hH f hpend

lemma false_of_three_core_adj_of_cliqueFree_three {C : Type} {H : SimpleGraph C}
    (hH : H.CliqueFree 3) {a b c : C}
    (hab : H.Adj a b) (hac : H.Adj a c) (hbc : H.Adj b c)
    (hab_ne : a ≠ b) (hac_ne : a ≠ c) (hbc_ne : b ≠ c) : False := by
  let g : Fin 3 → C := fun i =>
    match i with
    | 0 => a
    | 1 => b
    | 2 => c
  have ginj : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [g] at hij ⊢
    · exact False.elim (hab_ne hij)
    · exact False.elim (hac_ne hij)
    · exact False.elim (hab_ne hij.symm)
    · exact False.elim (hbc_ne hij)
    · exact False.elim (hac_ne hij.symm)
    · exact False.elim (hbc_ne hij.symm)
  let emb : completeGraph (Fin 3) ↪g H :=
    { toEmbedding := ⟨g, ginj⟩
      map_rel_iff' := by
        intro i j
        constructor
        · intro hij
          have hne : i ≠ j := by
            intro heq
            subst j
            exact H.irrefl hij
          simpa [top_adj] using hne
        · intro hij
          fin_cases i <;> fin_cases j <;> simp [g, top_adj] at hij ⊢
          · exact hab
          · exact hac
          · exact hab.symm
          · exact hbc
          · exact hac.symm
          · exact hbc.symm }
  exact (SimpleGraph.cliqueFree_iff.mp hH).false emb

/-- The hub supergraph used for feasibility is triangle-free when the core is triangle-free. -/
theorem pendantHubSupergraphSum_cliqueFree_three {C P : Type} {H : SimpleGraph C}
    {root : P → C} {hub : P} (hH : H.CliqueFree 3) :
    (PendantHubSupergraphSum H root hub).CliqueFree 3 := by
  rw [SimpleGraph.cliqueFree_iff]
  refine ⟨?_⟩
  intro f
  have h01 : (PendantHubSupergraphSum H root hub).Adj (f (0 : Fin 3)) (f 1) := by
    exact (RelEmbedding.map_rel_iff f).2 (by simp [top_adj])
  have h02 : (PendantHubSupergraphSum H root hub).Adj (f (0 : Fin 3)) (f 2) := by
    exact (RelEmbedding.map_rel_iff f).2 (by simp [top_adj])
  have h12 : (PendantHubSupergraphSum H root hub).Adj (f (1 : Fin 3)) (f 2) := by
    exact (RelEmbedding.map_rel_iff f).2 (by simp [top_adj])
  have hne01 : f (0 : Fin 3) ≠ f 1 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1) (RelEmbedding.injective f h)
  have hne02 : f (0 : Fin 3) ≠ f 2 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 2) (RelEmbedding.injective f h)
  have hne12 : f (1 : Fin 3) ≠ f 2 := by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2) (RelEmbedding.injective f h)
  cases h0 : f (0 : Fin 3) with
  | inl c0 =>
      cases h1 : f (1 : Fin 3) with
      | inl c1 =>
          cases h2 : f (2 : Fin 3) with
          | inl c2 =>
              have hc01 : H.Adj c0 c1 := by simpa [h0, h1] using h01
              have hc02 : H.Adj c0 c2 := by simpa [h0, h2] using h02
              have hc12 : H.Adj c1 c2 := by simpa [h1, h2] using h12
              have hnc01 : c0 ≠ c1 := by
                intro hc
                exact hne01 (by rw [h0, h1, hc])
              have hnc02 : c0 ≠ c2 := by
                intro hc
                exact hne02 (by rw [h0, h2, hc])
              have hnc12 : c1 ≠ c2 := by
                intro hc
                exact hne12 (by rw [h1, h2, hc])
              exact false_of_three_core_adj_of_cliqueFree_three hH hc01 hc02 hc12 hnc01 hnc02 hnc12
          | inr p2 =>
              have hr20 : root p2 = c0 := by simpa [h0, h2] using h02
              have hr21 : root p2 = c1 := by simpa [h1, h2] using h12
              have hnc01 : c0 ≠ c1 := by
                intro hc
                exact hne01 (by rw [h0, h1, hc])
              exact hnc01 (hr20.symm.trans hr21)
      | inr p1 =>
          cases h2 : f (2 : Fin 3) with
          | inl c2 =>
              have hr10 : root p1 = c0 := by simpa [h0, h1] using h01
              have hr12 : root p1 = c2 := by simpa [h1, h2] using h12
              have hnc02 : c0 ≠ c2 := by
                intro hc
                exact hne02 (by rw [h0, h2, hc])
              exact hnc02 (hr10.symm.trans hr12)
          | inr p2 =>
              have hr10 : root p1 = c0 := by simpa [h0, h1] using h01
              have hr20 : root p2 = c0 := by simpa [h0, h2] using h02
              have hp12 : (p1 = hub ∧ root p2 ≠ root hub) ∨
                  (p2 = hub ∧ root p1 ≠ root hub) := by
                simpa [h1, h2] using h12
              rcases hp12 with ⟨hp1, hroot⟩ | ⟨hp2, hroot⟩
              · subst p1
                exact hroot (hr20.trans hr10.symm)
              · subst p2
                exact hroot (hr10.trans hr20.symm)
  | inr p0 =>
      cases h1 : f (1 : Fin 3) with
      | inl c1 =>
          cases h2 : f (2 : Fin 3) with
          | inl c2 =>
              have hr01 : root p0 = c1 := by simpa [h0, h1] using h01
              have hr02 : root p0 = c2 := by simpa [h0, h2] using h02
              have hnc12 : c1 ≠ c2 := by
                intro hc
                exact hne12 (by rw [h1, h2, hc])
              exact hnc12 (hr01.symm.trans hr02)
          | inr p2 =>
              have hr01 : root p0 = c1 := by simpa [h0, h1] using h01
              have hr21 : root p2 = c1 := by simpa [h1, h2] using h12
              have hp02 : (p0 = hub ∧ root p2 ≠ root hub) ∨
                  (p2 = hub ∧ root p0 ≠ root hub) := by
                simpa [h0, h2] using h02
              rcases hp02 with ⟨hp0, hroot⟩ | ⟨hp2, hroot⟩
              · subst p0
                exact hroot (hr21.trans hr01.symm)
              · subst p2
                exact hroot (hr01.trans hr21.symm)
      | inr p1 =>
          cases h2 : f (2 : Fin 3) with
          | inl c2 =>
              have hr02 : root p0 = c2 := by simpa [h0, h2] using h02
              have hr12 : root p1 = c2 := by simpa [h1, h2] using h12
              have hp01 : (p0 = hub ∧ root p1 ≠ root hub) ∨
                  (p1 = hub ∧ root p0 ≠ root hub) := by
                simpa [h0, h1] using h01
              rcases hp01 with ⟨hp0, hroot⟩ | ⟨hp1, hroot⟩
              · subst p0
                exact hroot (hr12.trans hr02.symm)
              · subst p1
                exact hroot (hr02.trans hr12.symm)
          | inr p2 =>
              have hpne01 : p0 ≠ p1 := by
                intro hp
                exact hne01 (by rw [h0, h1, hp])
              have hpne02 : p0 ≠ p2 := by
                intro hp
                exact hne02 (by rw [h0, h2, hp])
              have hpne12 : p1 ≠ p2 := by
                intro hp
                exact hne12 (by rw [h1, h2, hp])
              have hp01 : (p0 = hub ∧ root p1 ≠ root hub) ∨
                  (p1 = hub ∧ root p0 ≠ root hub) := by
                simpa [h0, h1] using h01
              have hp02 : (p0 = hub ∧ root p2 ≠ root hub) ∨
                  (p2 = hub ∧ root p0 ≠ root hub) := by
                simpa [h0, h2] using h02
              have hp12 : (p1 = hub ∧ root p2 ≠ root hub) ∨
                  (p2 = hub ∧ root p1 ≠ root hub) := by
                simpa [h1, h2] using h12
              rcases hp01 with ⟨hp0, _⟩ | ⟨hp1, _⟩
              · rcases hp12 with ⟨hp1, _⟩ | ⟨hp2, _⟩
                · exact hpne01 (hp0.trans hp1.symm)
                · exact hpne02 (hp0.trans hp2.symm)
              · rcases hp02 with ⟨hp0, _⟩ | ⟨hp2, _⟩
                · exact hpne01 (hp0.trans hp1.symm)
                · exact hpne12 (hp1.trans hp2.symm)

/-- The core embeds into the sum-type pendant-core graph. -/
def pendantCoreGraphSumCoreHom {C P : Type} (H : SimpleGraph C) (root : P → C) :
    H →g PendantCoreGraphSum H root where
  toFun := Sum.inl
  map_rel' := by
    intro a b h
    exact h

/-- Adding pendant leaves to a connected core keeps the graph connected. -/
theorem pendantCoreGraphSum_connected {C P : Type} {H : SimpleGraph C} {root : P → C}
    (hH : H.Connected) : (PendantCoreGraphSum H root).Connected := by
  letI : Nonempty (C ⊕ P) := hH.nonempty.map Sum.inl
  refine ⟨?_⟩
  intro x y
  cases x with
  | inl a =>
      cases y with
      | inl b => exact (hH.preconnected a b).map (pendantCoreGraphSumCoreHom H root)
      | inr q =>
          exact ((hH.preconnected a (root q)).map (pendantCoreGraphSumCoreHom H root)).trans
            (Adj.reachable (by exact rfl)).symm
  | inr p =>
      cases y with
      | inl b =>
          exact (Adj.reachable (by exact rfl)).trans
            ((hH.preconnected (root p) b).map (pendantCoreGraphSumCoreHom H root))
      | inr q =>
          exact (Adj.reachable (by exact rfl)).trans
            (((hH.preconnected (root p) (root q)).map (pendantCoreGraphSumCoreHom H root)).trans
              (Adj.reachable (by exact rfl)).symm)

/-- The pendant vertices before transport: `s` indexed leaves over every core vertex, plus `q`
extra leaves.  The extras are attached to the first `q` core vertices when `q ≤ m`. -/
abbrev PendantCorePendant (s m q : ℕ) := (Fin m × Fin s) ⊕ Fin q

/-- The finite vertex type used before transporting the pendant-core graph to `Fin n`. -/
abbrev PendantCoreVertex (s m q : ℕ) := Fin m ⊕ PendantCorePendant s m q

/-- The root of a pendant in the faithful product/sum encoding. -/
def pendantCoreRoot {s m q : ℕ} (hq : q ≤ m) : PendantCorePendant s m q → Fin m
  | Sum.inl p => p.1
  | Sum.inr j => Fin.castLE hq j

/-- Pendants with a fixed root. -/
abbrev PendantRootFiber {s m q : ℕ} (hq : q ≤ m) (c : Fin m) :=
  {p : PendantCorePendant s m q // pendantCoreRoot hq p = c}

/-- A fiber code proving that each core supports at most `s + 1` pendants. -/
def pendantRootFiberCode {s m q : ℕ} {hq : q ≤ m} {c : Fin m} :
    PendantRootFiber (s := s) hq c → Fin s ⊕ Unit
  | ⟨Sum.inl p, _⟩ => Sum.inl p.2
  | ⟨Sum.inr _, _⟩ => Sum.inr ()

lemma pendantRootFiberCode_injective {s m q : ℕ} {hq : q ≤ m} {c : Fin m} :
    Function.Injective (pendantRootFiberCode (s := s) (hq := hq) (c := c)) := by
  rintro ⟨p, hp⟩ ⟨p', hp'⟩ hcode
  cases p with
  | inl p0 =>
      cases p' with
      | inl p1 =>
          simp [pendantRootFiberCode] at hcode
          have hroot0 : p0.1 = c := by simpa [pendantCoreRoot] using hp
          have hroot1 : p1.1 = c := by simpa [pendantCoreRoot] using hp'
          apply Subtype.ext
          exact congrArg Sum.inl (Prod.ext (hroot0.trans hroot1.symm) hcode)
      | inr j =>
          simp [pendantRootFiberCode] at hcode
  | inr j =>
      cases p' with
      | inl p1 =>
          simp [pendantRootFiberCode] at hcode
      | inr j' =>
          have hj : Fin.castLE hq j = c := by simpa [pendantCoreRoot] using hp
          have hj' : Fin.castLE hq j' = c := by simpa [pendantCoreRoot] using hp'
          have hcast : Fin.castLE hq j = Fin.castLE hq j' := hj.trans hj'.symm
          have hidx : j = j' := Fin.castLE_injective hq hcast
          apply Subtype.ext
          simp [hidx]

lemma pendantRootFiber_card_le {s m q : ℕ} (hq : q ≤ m) (c : Fin m) :
    Fintype.card (PendantRootFiber (s := s) hq c) ≤ s + 1 := by
  calc
    Fintype.card (PendantRootFiber (s := s) hq c) ≤ Fintype.card (Fin s ⊕ Unit) :=
      Fintype.card_le_of_injective
        (pendantRootFiberCode (s := s) (hq := hq) (c := c))
        (pendantRootFiberCode_injective (s := s) (hq := hq) (c := c))
    _ = s + 1 := by simp

lemma coreFreeComponentsAtRoot_card_le_typed {s m q : ℕ} (hq : q ≤ m)
    {K : SimpleGraph (PendantCoreVertex s m q)} (c : Fin m) :
    (CoreFreeComponentsAtRootFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq) c).card ≤
      s + 1 := by
  have h := coreFreeComponentsAtRoot_card_le_rootFiber
    (K := K) (root := pendantCoreRoot (s := s) (m := m) (q := q) hq) c
  have hfiber : Nat.card (PendantRootFiber (s := s) hq c) =
      Fintype.card (PendantRootFiber (s := s) hq c) := by
    rw [Nat.card_eq_fintype_card]
  exact h.trans (by simpa [PendantRootFiber, hfiber] using pendantRootFiber_card_le hq c)

lemma coreFreeComponent_card_le_typed_root_bound {s m q : ℕ} (hq : q ≤ m)
    {K : SimpleGraph (PendantCoreVertex s m q)} :
    (CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card ≤
      m * (s + 1) := by
  calc
    (CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card
        ≤ ∑ c : Fin m,
          (CoreFreeComponentsAtRootFinset K
            (pendantCoreRoot (s := s) (m := m) (q := q) hq) c).card :=
      coreFreeComponent_card_le_sum_roots
    _ ≤ ∑ _c : Fin m, (s + 1) := by
      exact Finset.sum_le_sum fun c _ => coreFreeComponentsAtRoot_card_le_typed (K := K) hq c
    _ = m * (s + 1) := by simp [Fintype.card_fin]

lemma pendantCorePendant_nat_card (s m q : ℕ) :
    Nat.card (PendantCorePendant s m q) = m * s + q := by
  rw [Nat.card_eq_fintype_card]
  dsimp [PendantCorePendant]
  simp [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]

lemma real_sub_le_of_nat_sub_le {a b c : ℕ} {x y : ℝ}
    (hx : x ≤ (a : ℝ)) (hy : (b : ℝ) ≤ y) (h : a - b ≤ c) :
    x - y ≤ (c : ℝ) := by
  by_cases hba : b ≤ a
  · have hc : (a : ℝ) - (b : ℝ) ≤ (c : ℝ) := by
      have hcast : ((a - b : ℕ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast h
      rwa [Nat.cast_sub hba] at hcast
    nlinarith
  · have hab : (a : ℝ) < (b : ℝ) := by exact_mod_cast Nat.lt_of_not_ge hba
    have hxy : x - y ≤ 0 := by nlinarith
    have hc0 : 0 ≤ (c : ℝ) := by positivity
    linarith


lemma coreFreeComponent_offDiag_card_le_typed {s m q : ℕ} (hq : q ≤ m)
    {K : SimpleGraph (PendantCoreVertex s m q)}
    (hKdiam : K.ediam ≤ (4 : ℕ∞)) :
    ((CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).offDiag).card ≤
      m * (s + 1) * (s + 1) + 2 * (CoreClosePairFinset K).card * (s + 1) * (s + 1) := by
  classical
  have h := coreFreeComponent_offDiag_card_le_root_close
    (C := Fin m) (P := PendantCorePendant s m q) (K := K)
    (root := pendantCoreRoot (s := s) (m := m) (q := q) hq) (S := s + 1)
    hKdiam (fun c => coreFreeComponentsAtRoot_card_le_typed (s := s) (m := m) (q := q)
      (K := K) hq c)
  simpa [Fintype.card_fin, Nat.mul_assoc] using h

lemma coreFreeComponent_sq_sub_card_le_typed {s m q : ℕ} (hq : q ≤ m)
    {K : SimpleGraph (PendantCoreVertex s m q)}
    (hKdiam : K.ediam ≤ (4 : ℕ∞)) :
    (CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card *
        (CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card -
      (CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card ≤
        m * (s + 1) * (s + 1) + 2 * (CoreClosePairFinset K).card * (s + 1) * (s + 1) := by
  simpa [Finset.offDiag_card] using coreFreeComponent_offDiag_card_le_typed (s := s) (m := m)
    (q := q) (K := K) hq hKdiam


lemma nat_le_mul_self (n : ℕ) : n ≤ n * n := by
  cases n with
  | zero => simp
  | succ n => exact Nat.le_mul_of_pos_right _ (Nat.succ_pos n)

lemma coreFreeComponent_sq_sub_real_le_typed {s m q : ℕ} (hq : q ≤ m)
    {K : SimpleGraph (PendantCoreVertex s m q)}
    (hKdiam : K.ediam ≤ (4 : ℕ∞)) :
    let N :=
      (CoreFreeComponentFinset K
        (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card
    (N : ℝ) * (N : ℝ) - (N : ℝ) ≤
      (m : ℝ) * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) +
        2 * ((CoreClosePairFinset K).card : ℝ) * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) := by
  intro N
  have hnat := coreFreeComponent_sq_sub_card_le_typed (s := s) (m := m) (q := q)
    (K := K) hq hKdiam
  have hcast : (((N * N - N : ℕ) : ℝ)) ≤
      (m * (s + 1) * (s + 1) + 2 * (CoreClosePairFinset K).card * (s + 1) * (s + 1) : ℕ) := by
    exact_mod_cast hnat
  have hle : N ≤ N * N := nat_le_mul_self N
  rw [Nat.cast_sub hle] at hcast
  norm_num at hcast ⊢
  nlinarith

lemma real_le_one_add_sqrt_of_sq_sub_le {x B : ℝ}
    (h : x * x - x ≤ B) :
    x ≤ 1 + Real.sqrt B := by
  by_cases hx1 : x ≤ 1
  · have hs : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
    linarith
  · have hxge : 1 ≤ x := le_of_not_ge hx1
    have hsq : (x - 1) ^ 2 ≤ B := by nlinarith
    have hs : x - 1 ≤ Real.sqrt B := Real.le_sqrt_of_sq_le hsq
    linarith


lemma coreFreeComponent_card_real_le_one_add_sqrt_of_close_bound {s m q : ℕ} (hq : q ≤ m)
    {K : SimpleGraph (PendantCoreVertex s m q)} {B : ℝ}
    (hKdiam : K.ediam ≤ (4 : ℕ∞))
    (hclose : ((CoreClosePairFinset K).card : ℝ) ≤ B) :
    let N :=
      (CoreFreeComponentFinset K
        (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card
    (N : ℝ) ≤
      1 + Real.sqrt
        ((m : ℝ) * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) +
          2 * B * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ)) := by
  intro N
  have hquad := coreFreeComponent_sq_sub_real_le_typed (s := s) (m := m) (q := q)
    (K := K) hq hKdiam
  have hroot := real_le_one_add_sqrt_of_sq_sub_le (x := (N : ℝ)) hquad
  refine hroot.trans ?_
  have hsqrt :
      Real.sqrt
          ((m : ℝ) * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) +
            2 * ((CoreClosePairFinset K).card : ℝ) * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ)) ≤
        Real.sqrt
          ((m : ℝ) * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) +
            2 * B * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ)) := by
    apply Real.sqrt_le_sqrt
    have hSsq : 0 ≤ ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  linarith


lemma coreFreeComponent_card_real_le_one_add_of_close_bound_sq {s m q : ℕ} (hq : q ≤ m)
    {K : SimpleGraph (PendantCoreVertex s m q)} {B R : ℝ}
    (hKdiam : K.ediam ≤ (4 : ℕ∞))
    (hclose : ((CoreClosePairFinset K).card : ℝ) ≤ B)
    (hR : 0 ≤ R)
    (hbound :
      (m : ℝ) * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) +
          2 * B * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) ≤ R ^ 2) :
    let N :=
      (CoreFreeComponentFinset K
        (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card
    (N : ℝ) ≤ 1 + R := by
  intro N
  have hN := coreFreeComponent_card_real_le_one_add_sqrt_of_close_bound (s := s) (m := m)
    (q := q) (K := K) hq hKdiam hclose
  have hsqrt :
      Real.sqrt
        ((m : ℝ) * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) +
          2 * B * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ)) ≤ R := by
    rw [Real.sqrt_le_iff]
    exact ⟨hR, hbound⟩
  linarith

lemma coreFreeComponent_card_real_le_one_add_sqrt_host {s d m q : ℕ} (hq : q ≤ m)
    {H : SimpleGraph (Fin m)} {K : SimpleGraph (PendantCoreVertex s m q)}
    (hHost : HostGraph d m H)
    (hGK : PendantCoreGraphSum H (pendantCoreRoot (s := s) (m := m) (q := q) hq) ≤ K)
    (hKtf : K.CliqueFree 3) (hKdiam : K.ediam ≤ (4 : ℕ∞)) :
    let A :=
      (AddedEdgeFinset
        (PendantCoreGraphSum H (pendantCoreRoot (s := s) (m := m) (q := q) hq)) K).card
    let S : ℝ := ((s + 1 : ℕ) : ℝ)
    let B : ℝ :=
      (m : ℝ) * (d : ℝ) + (m : ℝ) * (d : ℝ) * (d : ℝ) +
        (A : ℝ) * (1 + 2 * (hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ)))
    let N :=
      (CoreFreeComponentFinset K
        (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card
    (N : ℝ) ≤ 1 + Real.sqrt ((m : ℝ) * S * S + 2 * B * S * S) := by
  intro A S B N
  exact coreFreeComponent_card_real_le_one_add_sqrt_of_close_bound (s := s) (m := m)
    (q := q) (K := K) (B := B) hq hKdiam
    (by
      simpa [A, B] using
        (coreClosePair_card_real_le_host_log (d := d) (m := m)
          (P := PendantCorePendant s m q) (H := H)
          (root := pendantCoreRoot (s := s) (m := m) (q := q) hq) (K := K)
          hHost hGK hKtf))

lemma pendant_core_typed_added_edges_lower_of_coreFree_bound {s m q : ℕ} (hq : q ≤ m)
    {H : SimpleGraph (Fin m)} {K : SimpleGraph (PendantCoreVertex s m q)} {B : ℝ}
    (hfree :
      ((CoreFreeComponentFinset K
        (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card : ℝ) ≤ B) :
    ((m * s : ℕ) : ℝ) - B ≤
      ((AddedEdgeFinset
        (PendantCoreGraphSum H (pendantCoreRoot (s := s) (m := m) (q := q) hq)) K).card :
          ℝ) := by
  have hpend : ((m * s : ℕ) : ℝ) ≤
      (Nat.card (PendantCorePendant s m q) : ℝ) := by
    rw [pendantCorePendant_nat_card]
    exact_mod_cast Nat.le_add_right (m * s) q
  have hacc : Nat.card (PendantCorePendant s m q) -
      (CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card ≤
        (AddedEdgeFinset
          (PendantCoreGraphSum H (pendantCoreRoot (s := s) (m := m) (q := q) hq)) K).card :=
      by
    simpa using
      (pendant_component_accounting (C := Fin m) (P := PendantCorePendant s m q)
        (H := H) (root := pendantCoreRoot (s := s) (m := m) (q := q) hq) (K := K))
  exact real_sub_le_of_nat_sub_le hpend hfree hacc

lemma pendant_core_typed_added_edges_lower_of_coreFree_eta {s m q : ℕ} (hq : q ≤ m)
    {H : SimpleGraph (Fin m)} {K : SimpleGraph (PendantCoreVertex s m q)} {η : ℝ}
    (hfree :
      ((CoreFreeComponentFinset K
        (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card : ℝ) ≤
          η / 4 * ((m * s : ℕ) : ℝ) + 1) :
    (1 - η / 4) * ((m * s : ℕ) : ℝ) - 1 ≤
      ((AddedEdgeFinset
        (PendantCoreGraphSum H (pendantCoreRoot (s := s) (m := m) (q := q) hq)) K).card :
          ℝ) := by
  have h := pendant_core_typed_added_edges_lower_of_coreFree_bound (s := s) (m := m) (q := q)
    (H := H) (K := K) hq hfree
  nlinarith

/-- A canonical base pendant over a core vertex, available when `s > 0`. -/
def basePendant {s m q : ℕ} (hs : 0 < s) (c : Fin m) : PendantCorePendant s m q :=
  Sum.inl (c, ⟨0, hs⟩)

@[simp] lemma pendantCoreRoot_basePendant {s m q : ℕ} (hq : q ≤ m)
    (hs : 0 < s) (c : Fin m) :
    pendantCoreRoot (s := s) (m := m) (q := q) hq (basePendant hs c) = c := rfl

lemma pendantCoreRoot_cover_of_pos_s {s m q : ℕ} (hq : q ≤ m) (hs : 0 < s) :
    ∀ c : Fin m, ∃ p : PendantCorePendant s m q, pendantCoreRoot hq p = c := by
  intro c
  exact ⟨basePendant hs c, rfl⟩

lemma pendantHubTyped_ediam_le_four {s m q : ℕ} (hq : q ≤ m) (hm : 0 < m)
    (hs : 0 < s) (H : SimpleGraph (Fin m)) :
    (PendantHubSupergraphSum H (pendantCoreRoot (s := s) (m := m) (q := q) hq)
      (basePendant hs ⟨0, hm⟩)).ediam ≤ (4 : ℕ∞) := by
  apply pendantHubSupergraphSum_ediam_le_four
  intro c _
  exact pendantCoreRoot_cover_of_pos_s hq hs c

/-- The pendant-core graph on its natural sum-type vertex set. -/
def PendantCoreGraphTyped (s m q : ℕ) (hq : q ≤ m) (H : SimpleGraph (Fin m)) :
    SimpleGraph (PendantCoreVertex s m q) :=
  PendantCoreGraphSum H (pendantCoreRoot (s := s) (m := m) (q := q) hq)

lemma pendantCoreVertex_card (s m q : ℕ) :
    Fintype.card (PendantCoreVertex s m q) = m * (s + 1) + q := by
  dsimp [PendantCoreVertex, PendantCorePendant]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [Nat.mul_succ]
  omega

/-- The pendant-core construction used in the write-up, transported to the challenge's `Fin n`
vertex type when the cardinal arithmetic matches.  Outside the intended arithmetic and `q ≤ m`
range it is defined as `⊥`, which is irrelevant for the eventual construction. -/
def PendantCoreGraph (s n m q : ℕ) (H : SimpleGraph (Fin m)) : SimpleGraph (Fin n) :=
  if hq : q ≤ m then
    if hn : m * (s + 1) + q = n then
      (PendantCoreGraphTyped s m q hq H).overFin (by
        rw [pendantCoreVertex_card, hn])
    else
      ⊥
  else
    ⊥

lemma pendantCoreGraph_eq_overFin {s n m q : ℕ} {H : SimpleGraph (Fin m)}
    (hq : q ≤ m) (hn : m * (s + 1) + q = n) :
    PendantCoreGraph s n m q H =
      (PendantCoreGraphTyped s m q hq H).overFin (by rw [pendantCoreVertex_card, hn]) := by
  simp [PendantCoreGraph, hq, hn]

lemma pendantCoreGraph_connected {s n m q : ℕ} {H : SimpleGraph (Fin m)}
    (hq : q ≤ m) (hn : m * (s + 1) + q = n) (hH : H.Connected) :
    (PendantCoreGraph s n m q H).Connected := by
  rw [pendantCoreGraph_eq_overFin hq hn]
  exact (SimpleGraph.Iso.connected_iff
    (SimpleGraph.overFinIso (G := PendantCoreGraphTyped s m q hq H)
      (by rw [pendantCoreVertex_card, hn]))).1
    (pendantCoreGraphSum_connected hH)

lemma pendantCoreGraph_cliqueFree_three {s n m q : ℕ} {H : SimpleGraph (Fin m)}
    (hq : q ≤ m) (hn : m * (s + 1) + q = n) (hH : H.CliqueFree 3) :
    (PendantCoreGraph s n m q H).CliqueFree 3 := by
  rw [pendantCoreGraph_eq_overFin hq hn]
  exact SimpleGraph.CliqueFree.comap
    (SimpleGraph.overFinIso (G := PendantCoreGraphTyped s m q hq H)
      (by rw [pendantCoreVertex_card, hn])).symm.toEmbedding
    (pendantCoreGraphSum_cliqueFree_three hH)

lemma pendantCoreGraph_feasible {s n m q : ℕ} {H : SimpleGraph (Fin m)}
    (hq : q ≤ m) (hn : m * (s + 1) + q = n) (hm : 0 < m) (hs : 0 < s)
    (hH : H.CliqueFree 3) :
    ∃ K : SimpleGraph (Fin n), FeasibleSupergraph 4 (PendantCoreGraph s n m q H) K := by
  classical
  let root : PendantCorePendant s m q → Fin m :=
    pendantCoreRoot (s := s) (m := m) (q := q) hq
  let hub : PendantCorePendant s m q := basePendant hs ⟨0, hm⟩
  let Ksum : SimpleGraph (PendantCoreVertex s m q) := PendantHubSupergraphSum H root hub
  have hcard : Fintype.card (PendantCoreVertex s m q) = n := by
    rw [pendantCoreVertex_card, hn]
  refine ⟨Ksum.overFin hcard, ?_, ?_, ?_⟩
  · rw [pendantCoreGraph_eq_overFin hq hn]
    convert overFin_mono hcard (pendantCoreGraphSum_le_hubSupergraph H root hub) using 1
  · exact SimpleGraph.CliqueFree.comap
      (SimpleGraph.overFinIso (G := Ksum) hcard).symm.toEmbedding
      (pendantHubSupergraphSum_cliqueFree_three (H := H) (root := root) (hub := hub) hH)
  · have hcover : ∀ c : Fin m, c ≠ root hub →
        ∃ p : PendantCorePendant s m q, root p = c := by
      intro c _
      simpa [root] using pendantCoreRoot_cover_of_pos_s hq hs c
    exact overFin_ediam_le_of_forall_exists_walk_le Ksum hcard
      (pendantHubSupergraphSum_walk_le_four H root hub hcover)

/-- Specification for `PendantCoreGraph`: connected, triangle-free, and built from a host core with
`s` or `s + 1` leaves on each core vertex. -/
def PendantCoreSpec (s d n m q : ℕ) (H : SimpleGraph (Fin m)) : Prop :=
  n = m * (s + 1) + q ∧ q ≤ s ∧ HostGraph d m H

lemma PendantCoreSpec.order {s d n m q : ℕ} {H : SimpleGraph (Fin m)}
    (h : PendantCoreSpec s d n m q H) : n = m * (s + 1) + q := h.1

lemma PendantCoreSpec.remainder_le {s d n m q : ℕ} {H : SimpleGraph (Fin m)}
    (h : PendantCoreSpec s d n m q H) : q ≤ s := h.2.1

lemma PendantCoreSpec.host {s d n m q : ℕ} {H : SimpleGraph (Fin m)}
    (h : PendantCoreSpec s d n m q H) : HostGraph d m H := h.2.2

lemma PendantCoreSpec.graph_connected {s d n m q : ℕ} {H : SimpleGraph (Fin m)}
    (h : PendantCoreSpec s d n m q H) (hq : q ≤ m) :
    (PendantCoreGraph s n m q H).Connected :=
  pendantCoreGraph_connected hq h.order.symm h.host.connected

lemma PendantCoreSpec.graph_cliqueFree_three {s d n m q : ℕ} {H : SimpleGraph (Fin m)}
    (h : PendantCoreSpec s d n m q H) (hq : q ≤ m) :
    (PendantCoreGraph s n m q H).CliqueFree 3 :=
  pendantCoreGraph_cliqueFree_three hq h.order.symm h.host.cliqueFree_three

lemma PendantCoreSpec.graph_feasible {s d n m q : ℕ} {H : SimpleGraph (Fin m)}
    (h : PendantCoreSpec s d n m q H) (hq : q ≤ m) (hm : 0 < m) (hs : 0 < s) :
    ∃ K : SimpleGraph (Fin n), FeasibleSupergraph 4 (PendantCoreGraph s n m q H) K :=
  pendantCoreGraph_feasible hq h.order.symm hm hs h.host.cliqueFree_three

/-- Pull the typed component-count estimate through the canonical `Fin n` transport to bound any
feasible `Fin n` supergraph of a pendant-core graph. -/
theorem pendantCoreGraph_addedEdgeCount_lower_of_coreFree_eta {s n m q : ℕ}
    {H : SimpleGraph (Fin m)} (hq : q ≤ m) (hn : m * (s + 1) + q = n) {η : ℝ}
    (hfree : ∀ K : SimpleGraph (PendantCoreVertex s m q),
      PendantCoreGraphTyped s m q hq H ≤ K → K.CliqueFree 3 → K.ediam ≤ (4 : ℕ∞) →
        ((CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card : ℝ) ≤
          η / 4 * ((m * s : ℕ) : ℝ) + 1)
    (Kfin : SimpleGraph (Fin n))
    (hK : FeasibleSupergraph 4 (PendantCoreGraph s n m q H) Kfin) :
    (1 - η / 4) * ((m * s : ℕ) : ℝ) - 1 ≤
      (addedEdgeCount (PendantCoreGraph s n m q H) Kfin : ℝ) := by
  classical
  let Gt : SimpleGraph (PendantCoreVertex s m q) := PendantCoreGraphTyped s m q hq H
  have hc : Fintype.card (PendantCoreVertex s m q) = n := by
    rw [pendantCoreVertex_card, hn]
  let e := Fintype.equivFinOfCardEq hc
  let Kt : SimpleGraph (PendantCoreVertex s m q) := Kfin.comap e
  have hgraph : PendantCoreGraph s n m q H = Gt.overFin hc := by
    simpa [Gt] using pendantCoreGraph_eq_overFin (s := s) (n := n) (m := m) (q := q)
      (H := H) hq hn
  have hGKfin : Gt.overFin hc ≤ Kfin := by
    rw [← hgraph]
    exact hK.1
  have hGtKt : Gt ≤ Kt := by
    simpa [Gt, Kt, e] using overFin_le_comap_of_le (G := Gt) (K := Kfin) hc hGKfin
  have hKttf : Kt.CliqueFree 3 := by
    simpa [Kt, e] using cliqueFree_comap_equiv e hK.2.1
  have hKtdiam : Kt.ediam ≤ (4 : ℕ∞) := by
    simpa [Kt, e] using ediam_comap_equiv_le e hK.2.2
  have hfreeKt := hfree Kt hGtKt hKttf hKtdiam
  have htyped := pendant_core_typed_added_edges_lower_of_coreFree_eta
    (s := s) (m := m) (q := q) (H := H) (K := Kt) hq hfreeKt
  have hcount : addedEdgeCount (PendantCoreGraph s n m q H) Kfin =
      (AddedEdgeFinset Gt Kt).card := by
    rw [hgraph]
    simpa [Gt, Kt, e] using addedEdgeCount_overFin_eq_addedEdgeFinset_comap Gt Kfin hc
  rw [hcount]
  simpa [Gt, Kt] using htyped

/-- Under the typed core-free-component estimate, the actual `h_4` value for the transported
pendant-core graph has the same lower bound. -/
theorem PendantCoreSpec.exists_isHR_lower_of_coreFree_eta {s d n m q : ℕ}
    {H : SimpleGraph (Fin m)} (h : PendantCoreSpec s d n m q H)
    (hq : q ≤ m) (hm : 0 < m) (hs : 0 < s) {η : ℝ}
    (hfree : ∀ K : SimpleGraph (PendantCoreVertex s m q),
      PendantCoreGraphTyped s m q hq H ≤ K → K.CliqueFree 3 → K.ediam ≤ (4 : ℕ∞) →
        ((CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card : ℝ) ≤
          η / 4 * ((m * s : ℕ) : ℝ) + 1) :
    ∃ mhr : ℕ, IsHR 4 (PendantCoreGraph s n m q H) mhr ∧
      (1 - η / 4) * ((m * s : ℕ) : ℝ) - 1 ≤ (mhr : ℝ) := by
  refine exists_isHR_with_real_lower_bound
    (r := 4) (G := PendantCoreGraph s n m q H)
    (L := (1 - η / 4) * ((m * s : ℕ) : ℝ) - 1)
    (h.graph_feasible hq hm hs) ?_
  intro K hK
  exact pendantCoreGraph_addedEdgeCount_lower_of_coreFree_eta hq h.order.symm hfree K hK

/-- The same fixed-parameter statement after the final numerical absorption step. -/
theorem PendantCoreSpec.exists_isHR_final_of_coreFree_eta {s d n m q : ℕ}
    {H : SimpleGraph (Fin m)} (h : PendantCoreSpec s d n m q H)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hq : q ≤ m) (hm : 0 < m) (hs : 0 < s)
    (hfree : ∀ K : SimpleGraph (PendantCoreVertex s m q),
      PendantCoreGraphTyped s m q hq H ≤ K → K.CliqueFree 3 → K.ediam ≤ (4 : ℕ∞) →
        ((CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card : ℝ) ≤
          η / 4 * ((m * s : ℕ) : ℝ) + 1)
    (hsmn : (1 - η / 2) * (n : ℝ) ≤ ((m * s : ℕ) : ℝ))
    (hbig : 1 ≤ η / 4 * (n : ℝ)) :
    ∃ mhr : ℕ, IsHR 4 (PendantCoreGraph s n m q H) mhr ∧
      (1 - η) * (n : ℝ) ≤ (mhr : ℝ) := by
  rcases h.exists_isHR_lower_of_coreFree_eta hq hm hs hfree with ⟨mhr, hhr, hlower⟩
  refine ⟨mhr, hhr, ?_⟩
  have hcoef : 0 ≤ 1 - η / 4 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hsmn hcoef
  nlinarith

/-- Fixed-parameter counterexample package, after all graph-counting and numeric hypotheses have
been supplied. -/
theorem PendantCoreSpec.counterexample_of_coreFree_eta {s d n m q : ℕ}
    {H : SimpleGraph (Fin m)} (h : PendantCoreSpec s d n m q H)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hq : q ≤ m) (hm : 0 < m) (hs : 0 < s)
    (hfree : ∀ K : SimpleGraph (PendantCoreVertex s m q),
      PendantCoreGraphTyped s m q hq H ≤ K → K.CliqueFree 3 → K.ediam ≤ (4 : ℕ∞) →
        ((CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card : ℝ) ≤
          η / 4 * ((m * s : ℕ) : ℝ) + 1)
    (hsmn : (1 - η / 2) * (n : ℝ) ≤ ((m * s : ℕ) : ℝ))
    (hbig : 1 ≤ η / 4 * (n : ℝ)) :
    ∃ (G : SimpleGraph (Fin n)) (mhr : ℕ),
      G.Connected ∧ G.CliqueFree 3 ∧ IsHR 4 G mhr ∧ (1 - η) * (n : ℝ) ≤ (mhr : ℝ) := by
  rcases h.exists_isHR_final_of_coreFree_eta hη0 hη1 hq hm hs hfree hsmn hbig with
    ⟨mhr, hhr, hlower⟩
  exact ⟨PendantCoreGraph s n m q H, mhr, h.graph_connected hq, h.graph_cliqueFree_three hq,
    hhr, hlower⟩



/-- The elementary size comparison used after writing `n = m(s+1)+q` with `q ≤ s`. -/
lemma sm_lower_bound_of_order_le_mul_s_add_two {η : ℝ} {s m n : ℕ}
    (hη0 : 0 < η) (hη1 : η < 1)
    (hs : 4 ≤ η * ((s : ℝ) + 2))
    (hn : (n : ℝ) ≤ (m : ℝ) * ((s : ℝ) + 2)) :
    (1 - η / 2) * (n : ℝ) ≤ ((m * s : ℕ) : ℝ) := by
  have hcoef_nonneg : 0 ≤ 1 - η / 2 := by nlinarith
  have hstep₁ := mul_le_mul_of_nonneg_left hn hcoef_nonneg
  have hcoef : (1 - η / 2) * ((s : ℝ) + 2) ≤ (s : ℝ) := by nlinarith
  have hmnonneg : 0 ≤ (m : ℝ) := by positivity
  have hstep₂ : (1 - η / 2) * ((m : ℝ) * ((s : ℝ) + 2)) ≤ (m : ℝ) * (s : ℝ) := by
    have := mul_le_mul_of_nonneg_left hcoef hmnonneg
    nlinarith
  norm_num at hstep₁ hstep₂ ⊢
  nlinarith



lemma exists_nat_pos_eta_mul_add_two_ge_four {η : ℝ} (hη0 : 0 < η) :
    ∃ s : ℕ, 0 < s ∧ 4 ≤ η * ((s : ℝ) + 2) := by
  let s : ℕ := Nat.ceil (4 / η)
  have hsceil : (4 / η : ℝ) ≤ (s : ℝ) := Nat.le_ceil _
  have hspos : 0 < s := by
    have hsone : 1 ≤ s := by
      rw [Nat.one_le_ceil_iff]
      positivity
    exact Nat.succ_le_iff.mp hsone
  refine ⟨s, hspos, ?_⟩
  have hmul : η * (4 / η) ≤ η * (s : ℝ) := mul_le_mul_of_nonneg_left hsceil hη0.le
  have hηne : η ≠ 0 := ne_of_gt hη0
  have hmul_eq : η * (4 / η) = 4 := by
    field_simp [hηne]
  nlinarith [hmul, hmul_eq]

lemma eventually_atTop_div_succ {s : ℕ} {P : ℕ → Prop}
    (hP : ∀ᶠ m : ℕ in Filter.atTop, P m) :
    ∀ᶠ n : ℕ in Filter.atTop, P (n / (s + 1)) := by
  rcases Filter.eventually_atTop.1 hP with ⟨M, hM⟩
  refine Filter.eventually_atTop.2 ⟨(s + 1) * M, ?_⟩
  intro n hn
  apply hM
  change M ≤ n / (s + 1)
  rw [Nat.le_div_iff_mul_le (Nat.succ_pos s)]
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hn

lemma eventually_mod_succ_le_div_succ (s : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, n % (s + 1) ≤ n / (s + 1) := by
  refine Filter.eventually_atTop.2 ⟨(s + 1) * s, ?_⟩
  intro n hn
  have hmod : n % (s + 1) ≤ s := Nat.lt_succ_iff.mp (Nat.mod_lt n (Nat.succ_pos s))
  have hdiv : s ≤ n / (s + 1) := by
    rw [Nat.le_div_iff_mul_le (Nat.succ_pos s)]
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hn
  exact hmod.trans hdiv

lemma eventually_pos_div_succ (s : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, 0 < n / (s + 1) := by
  refine Filter.eventually_atTop.2 ⟨s + 1, ?_⟩
  intro n hn
  exact Nat.div_pos hn (Nat.succ_pos s)

lemma eventually_one_le_eta_four_mul_nat {η : ℝ} (hη0 : 0 < η) :
    ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ η / 4 * (n : ℝ) := by
  have hcoef : 0 < η / 4 := by positivity
  have ht : Filter.Tendsto (fun n : ℕ => η / 4 * (n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hcoef tendsto_natCast_atTop_atTop
  exact ht.eventually_ge_atTop 1

/-- Convert the component accounting inequality `t ≥ |I| - N` and the component bound on `N`
into the lower bound used in the final assembly. -/
theorem accounting_to_sm_lower_bound {η sm I N t : ℝ}
    (hacc : I - N ≤ t) (hI : sm ≤ I) (hN : N ≤ η / 4 * sm + 1) :
    (1 - η / 4) * sm - 1 ≤ t := by
  nlinarith

/-- The final real-arithmetic assembly from the write-up.  Once the component accounting gives
`t ≥ (1 - η/4) sm - 1`, it is enough that `sm` is at least `(1 - η/2)n` and `n` is large enough
to absorb the final `-1`. -/
theorem final_numeric_assembly {η sm n t : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (ht : (1 - η / 4) * sm - 1 ≤ t)
    (hsmn : (1 - η / 2) * n ≤ sm)
    (hbig : 1 ≤ η / 4 * n) :
    (1 - η) * n ≤ t := by
  have hcoef : 0 ≤ 1 - η / 4 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hsmn hcoef
  nlinarith

/-- A combined version of the last two deterministic arithmetic steps. -/
theorem final_assembly_from_accounting {η sm I N n t : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hacc : I - N ≤ t) (hI : sm ≤ I) (hN : N ≤ η / 4 * sm + 1)
    (hsmn : (1 - η / 2) * n ≤ sm) (hbig : 1 ≤ η / 4 * n) :
    (1 - η) * n ≤ t := by
  exact final_numeric_assembly hη0 hη1 (accounting_to_sm_lower_bound hacc hI hN) hsmn hbig


/-- Conditional fixed-parameter lower bound matching the corrected Lemma 3 argument: if the
supergraph already adds at least `n` edges, the final lower bound is immediate; otherwise the
core-free-component estimate is invoked. -/
theorem pendantCoreGraph_addedEdgeCount_final_lower_of_cond_coreFree_eta {s n m q : ℕ}
    {H : SimpleGraph (Fin m)} (hq : q ≤ m) (hn : m * (s + 1) + q = n)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hfree : ∀ K : SimpleGraph (PendantCoreVertex s m q),
      PendantCoreGraphTyped s m q hq H ≤ K → K.CliqueFree 3 → K.ediam ≤ (4 : ℕ∞) →
        ((AddedEdgeFinset (PendantCoreGraphTyped s m q hq H) K).card : ℝ) < (n : ℝ) →
          ((CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card : ℝ) ≤
            η / 4 * ((m * s : ℕ) : ℝ) + 1)
    (hsmn : (1 - η / 2) * (n : ℝ) ≤ ((m * s : ℕ) : ℝ))
    (hbig : 1 ≤ η / 4 * (n : ℝ))
    (Kfin : SimpleGraph (Fin n))
    (hK : FeasibleSupergraph 4 (PendantCoreGraph s n m q H) Kfin) :
    (1 - η) * (n : ℝ) ≤ (addedEdgeCount (PendantCoreGraph s n m q H) Kfin : ℝ) := by
  classical
  let Gt : SimpleGraph (PendantCoreVertex s m q) := PendantCoreGraphTyped s m q hq H
  have hc : Fintype.card (PendantCoreVertex s m q) = n := by
    rw [pendantCoreVertex_card, hn]
  let e := Fintype.equivFinOfCardEq hc
  let Kt : SimpleGraph (PendantCoreVertex s m q) := Kfin.comap e
  have hgraph : PendantCoreGraph s n m q H = Gt.overFin hc := by
    simpa [Gt] using pendantCoreGraph_eq_overFin (s := s) (n := n) (m := m) (q := q)
      (H := H) hq hn
  have hGKfin : Gt.overFin hc ≤ Kfin := by
    rw [← hgraph]
    exact hK.1
  have hGtKt : Gt ≤ Kt := by
    simpa [Gt, Kt, e] using overFin_le_comap_of_le (G := Gt) (K := Kfin) hc hGKfin
  have hKttf : Kt.CliqueFree 3 := by
    simpa [Kt, e] using cliqueFree_comap_equiv e hK.2.1
  have hKtdiam : Kt.ediam ≤ (4 : ℕ∞) := by
    simpa [Kt, e] using ediam_comap_equiv_le e hK.2.2
  have hcount : addedEdgeCount (PendantCoreGraph s n m q H) Kfin =
      (AddedEdgeFinset Gt Kt).card := by
    rw [hgraph]
    simpa [Gt, Kt, e] using addedEdgeCount_overFin_eq_addedEdgeFinset_comap Gt Kfin hc
  by_cases hsmall : ((AddedEdgeFinset Gt Kt).card : ℝ) < (n : ℝ)
  · have hfreeKt :
        ((CoreFreeComponentFinset Kt (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card : ℝ) ≤
          η / 4 * ((m * s : ℕ) : ℝ) + 1 := by
      exact hfree Kt (by simpa [Gt] using hGtKt) hKttf hKtdiam (by simpa [Gt] using hsmall)
    have htyped := pendant_core_typed_added_edges_lower_of_coreFree_eta
      (s := s) (m := m) (q := q) (H := H) (K := Kt) hq hfreeKt
    have hfinal := final_numeric_assembly hη0 hη1 htyped hsmn hbig
    rw [hcount]
    simpa [Gt, Kt] using hfinal
  · have hlarge : (n : ℝ) ≤ ((AddedEdgeFinset Gt Kt).card : ℝ) := le_of_not_gt hsmall
    have hcoef : (1 - η) * (n : ℝ) ≤ (n : ℝ) := by
      have hnnonneg : 0 ≤ (n : ℝ) := by positivity
      nlinarith
    have hfinal : (1 - η) * (n : ℝ) ≤ ((AddedEdgeFinset Gt Kt).card : ℝ) := hcoef.trans hlarge
    rw [hcount]
    simpa [Gt, Kt] using hfinal

/-- Fixed-parameter counterexample package with the corrected conditional Lemma 3 hypothesis. -/
theorem PendantCoreSpec.counterexample_of_cond_coreFree_eta {s d n m q : ℕ}
    {H : SimpleGraph (Fin m)} (h : PendantCoreSpec s d n m q H)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hq : q ≤ m) (hm : 0 < m) (hs : 0 < s)
    (hfree : ∀ K : SimpleGraph (PendantCoreVertex s m q),
      PendantCoreGraphTyped s m q hq H ≤ K → K.CliqueFree 3 → K.ediam ≤ (4 : ℕ∞) →
        ((AddedEdgeFinset (PendantCoreGraphTyped s m q hq H) K).card : ℝ) < (n : ℝ) →
          ((CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card : ℝ) ≤
            η / 4 * ((m * s : ℕ) : ℝ) + 1)
    (hsmn : (1 - η / 2) * (n : ℝ) ≤ ((m * s : ℕ) : ℝ))
    (hbig : 1 ≤ η / 4 * (n : ℝ)) :
    ∃ (G : SimpleGraph (Fin n)) (mhr : ℕ),
      G.Connected ∧ G.CliqueFree 3 ∧ IsHR 4 G mhr ∧ (1 - η) * (n : ℝ) ≤ (mhr : ℝ) := by
  have hlowerAll : ∀ K : SimpleGraph (Fin n), FeasibleSupergraph 4 (PendantCoreGraph s n m q H) K →
      (1 - η) * (n : ℝ) ≤ (addedEdgeCount (PendantCoreGraph s n m q H) K : ℝ) := by
    intro K hK
    exact pendantCoreGraph_addedEdgeCount_final_lower_of_cond_coreFree_eta
      (s := s) (n := n) (m := m) (q := q) (H := H) hq h.order.symm hη0 hη1
      hfree hsmn hbig K hK
  rcases exists_isHR_with_real_lower_bound
      (r := 4) (G := PendantCoreGraph s n m q H) (L := (1 - η) * (n : ℝ))
      (h.graph_feasible hq hm hs) hlowerAll with
    ⟨mhr, hhr, hlower⟩
  exact ⟨PendantCoreGraph s n m q H, mhr, h.graph_connected hq, h.graph_cliqueFree_three hq,
    hhr, hlower⟩


/-- Fixed-parameter counterexample package where Lemma 3 has been reduced to a single explicit
radicand inequality.  This is the deterministic interface for the remaining asymptotic estimates. -/
theorem PendantCoreSpec.counterexample_of_numeric_coreFree {s d n m q : ℕ}
    {H : SimpleGraph (Fin m)} (h : PendantCoreSpec s d n m q H)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hq : q ≤ m) (hm : 0 < m) (hs : 0 < s)
    (hrad : ∀ A : ℕ, (A : ℝ) < (n : ℝ) →
      let S : ℝ := ((s + 1 : ℕ) : ℝ)
      let B : ℝ :=
        (m : ℝ) * (d : ℝ) + (m : ℝ) * (d : ℝ) * (d : ℝ) +
          (A : ℝ) * (1 + 2 * (hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ)))
      (m : ℝ) * S * S + 2 * B * S * S ≤ (η / 4 * ((m * s : ℕ) : ℝ)) ^ 2)
    (hsmn : (1 - η / 2) * (n : ℝ) ≤ ((m * s : ℕ) : ℝ))
    (hbig : 1 ≤ η / 4 * (n : ℝ)) :
    ∃ (G : SimpleGraph (Fin n)) (mhr : ℕ),
      G.Connected ∧ G.CliqueFree 3 ∧ IsHR 4 G mhr ∧ (1 - η) * (n : ℝ) ≤ (mhr : ℝ) := by
  refine h.counterexample_of_cond_coreFree_eta hη0 hη1 hq hm hs ?_ hsmn hbig
  intro K hGK hKtf hKdiam hsmall
  let A := (AddedEdgeFinset (PendantCoreGraphTyped s m q hq H) K).card
  let S : ℝ := ((s + 1 : ℕ) : ℝ)
  let B : ℝ :=
    (m : ℝ) * (d : ℝ) + (m : ℝ) * (d : ℝ) * (d : ℝ) +
      (A : ℝ) * (1 + 2 * (hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ)))
  have hclose : ((CoreClosePairFinset K).card : ℝ) ≤ B := by
    simpa [A, B, PendantCoreGraphTyped] using
      (coreClosePair_card_real_le_host_log (d := d) (m := m)
        (P := PendantCorePendant s m q) (H := H)
        (root := pendantCoreRoot (s := s) (m := m) (q := q) hq) (K := K)
        h.host (by simpa [PendantCoreGraphTyped] using hGK) hKtf)
  have hR : 0 ≤ η / 4 * ((m * s : ℕ) : ℝ) := by positivity
  have hradA :
      (m : ℝ) * S * S + 2 * B * S * S ≤ (η / 4 * ((m * s : ℕ) : ℝ)) ^ 2 := by
    simpa [A, S, B] using hrad A hsmall
  have hN := coreFreeComponent_card_real_le_one_add_of_close_bound_sq
    (s := s) (m := m) (q := q) (K := K) (B := B)
    (R := η / 4 * ((m * s : ℕ) : ℝ)) hq hKdiam hclose hR hradA
  nlinarith



/-- Build the eventual finite pendant-core specifications from fixed `s,d`, eventual host graphs at
that `d`, and the explicit radicand estimate along `m = n / (s + 1)`. -/
theorem eventual_pendant_specs_of_fixed_d {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    {s d : ℕ} (hs : 0 < s) (hsη : 4 ≤ η * ((s : ℝ) + 2))
    (hHost : ∀ᶠ m : ℕ in Filter.atTop, ∃ H : SimpleGraph (Fin m), HostGraph d m H)
    (hrad : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ A : ℕ, (A : ℝ) < (n : ℝ) →
        let m := n / (s + 1)
        let S : ℝ := ((s + 1 : ℕ) : ℝ)
        let B : ℝ :=
          (m : ℝ) * (d : ℝ) + (m : ℝ) * (d : ℝ) * (d : ℝ) +
            (A : ℝ) * (1 + 2 * (hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ)))
        (m : ℝ) * S * S + 2 * B * S * S ≤ (η / 4 * ((m * s : ℕ) : ℝ)) ^ 2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ (s' d' m q : ℕ) (H : SimpleGraph (Fin m)),
        PendantCoreSpec s' d' n m q H ∧ q ≤ m ∧ 0 < m ∧ 0 < s' ∧
          (∀ A : ℕ, (A : ℝ) < (n : ℝ) →
            let S : ℝ := ((s' + 1 : ℕ) : ℝ)
            let B : ℝ :=
              (m : ℝ) * (d' : ℝ) + (m : ℝ) * (d' : ℝ) * (d' : ℝ) +
                (A : ℝ) * (1 + 2 * (hostC * (m : ℝ) * Real.log (d' : ℝ) / (d' : ℝ)))
            (m : ℝ) * S * S + 2 * B * S * S ≤ (η / 4 * ((m * s' : ℕ) : ℝ)) ^ 2) ∧
          (1 - η / 2) * (n : ℝ) ≤ ((m * s' : ℕ) : ℝ) ∧
          1 ≤ η / 4 * (n : ℝ) := by
  filter_upwards [eventually_atTop_div_succ (s := s) hHost, hrad,
    eventually_mod_succ_le_div_succ s, eventually_pos_div_succ s,
    eventually_one_le_eta_four_mul_nat hη0] with n hHostn hradn hqle hmpos hbig
  let m := n / (s + 1)
  let q := n % (s + 1)
  rcases hHostn with ⟨H, hH⟩
  have hqles : q ≤ s := by
    exact Nat.lt_succ_iff.mp (Nat.mod_lt n (Nat.succ_pos s))
  have hn : n = m * (s + 1) + q := by
    simpa [m, q, Nat.mul_comm] using (Nat.div_add_mod n (s + 1)).symm
  have hnle_nat : n ≤ m * (s + 2) := by
    calc
      n = m * (s + 1) + q := hn
      _ ≤ m * (s + 1) + m := Nat.add_le_add_left hqle _
      _ = m * (s + 2) := by ring
  have hnle : (n : ℝ) ≤ (m : ℝ) * ((s : ℝ) + 2) := by
    exact_mod_cast hnle_nat
  have hsmn : (1 - η / 2) * (n : ℝ) ≤ ((m * s : ℕ) : ℝ) :=
    sm_lower_bound_of_order_le_mul_s_add_two hη0 hη1 hsη hnle
  refine ⟨s, d, m, q, H, ?_, hqle, hmpos, hs, ?_, hsmn, hbig⟩
  · exact ⟨hn, hqles, hH⟩
  · intro A hA
    simpa [m] using hradn A hA

/-- Eventual counterexample family from eventual finite pendant-core specifications.  This isolates
what remains of the asymptotic parameter-selection proof after the deterministic graph counting. -/
theorem counterexample_family_from_eventual_pendant_specs {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hSpecs : ∀ᶠ n : ℕ in Filter.atTop,
      ∃ (s d m q : ℕ) (H : SimpleGraph (Fin m)),
        PendantCoreSpec s d n m q H ∧ q ≤ m ∧ 0 < m ∧ 0 < s ∧
          (∀ A : ℕ, (A : ℝ) < (n : ℝ) →
            let S : ℝ := ((s + 1 : ℕ) : ℝ)
            let B : ℝ :=
              (m : ℝ) * (d : ℝ) + (m : ℝ) * (d : ℝ) * (d : ℝ) +
                (A : ℝ) * (1 + 2 * (hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ)))
            (m : ℝ) * S * S + 2 * B * S * S ≤ (η / 4 * ((m * s : ℕ) : ℝ)) ^ 2) ∧
          (1 - η / 2) * (n : ℝ) ≤ ((m * s : ℕ) : ℝ) ∧
          1 ≤ η / 4 * (n : ℝ)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ (G : SimpleGraph (Fin n)) (mhr : ℕ),
        G.Connected ∧ G.CliqueFree 3 ∧ IsHR 4 G mhr ∧ (1 - η) * (n : ℝ) ≤ (mhr : ℝ) := by
  filter_upwards [hSpecs] with n hn
  rcases hn with ⟨s, d, m, q, H, hspec, hq, hm, hs, hrad, hsmn, hbig⟩
  exact hspec.counterexample_of_numeric_coreFree hη0 hη1 hq hm hs hrad hsmn hbig


/-- Counterexample family from fixed `s,d` data: eventual host graphs at `d` and the eventual
radicand estimate along the Euclidean decomposition of `n`. -/
theorem counterexample_family_from_fixed_d_data {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    {s d : ℕ} (hs : 0 < s) (hsη : 4 ≤ η * ((s : ℝ) + 2))
    (hHost : ∀ᶠ m : ℕ in Filter.atTop, ∃ H : SimpleGraph (Fin m), HostGraph d m H)
    (hrad : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ A : ℕ, (A : ℝ) < (n : ℝ) →
        let m := n / (s + 1)
        let S : ℝ := ((s + 1 : ℕ) : ℝ)
        let B : ℝ :=
          (m : ℝ) * (d : ℝ) + (m : ℝ) * (d : ℝ) * (d : ℝ) +
            (A : ℝ) * (1 + 2 * (hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ)))
        (m : ℝ) * S * S + 2 * B * S * S ≤ (η / 4 * ((m * s : ℕ) : ℝ)) ^ 2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ (G : SimpleGraph (Fin n)) (mhr : ℕ),
        G.Connected ∧ G.CliqueFree 3 ∧ IsHR 4 G mhr ∧ (1 - η) * (n : ℝ) ≤ (mhr : ℝ) := by
  exact counterexample_family_from_eventual_pendant_specs hη0 hη1
    (eventual_pendant_specs_of_fixed_d hη0 hη1 hs hsη hHost hrad)

lemma eventually_log_div_nat_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : ℕ in Filter.atTop, Real.log (d : ℝ) / (d : ℝ) ≤ ε := by
  have hlo : (fun x : ℝ => Real.log x) =o[Filter.atTop] (fun x : ℝ => x) :=
    Real.isLittleO_log_id_atTop
  have hlo_nat :
      (fun d : ℕ => Real.log (d : ℝ)) =o[Filter.atTop] (fun d : ℕ => (d : ℝ)) :=
    hlo.comp_tendsto tendsto_natCast_atTop_atTop
  have h := hlo_nat.def hε
  filter_upwards [h, Filter.eventually_ge_atTop 1] with d hd hd1
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
  have hlog : Real.log (d : ℝ) ≤ ε * (d : ℝ) := by
    have habs := hd
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at habs
    have hdabs : |(d : ℝ)| = (d : ℝ) := abs_of_nonneg (Nat.cast_nonneg d)
    rw [hdabs] at habs
    exact (le_abs_self _).trans habs
  exact (div_le_iff₀ hdpos).mpr hlog

lemma radicand_bound_real {η m n A S s d L : ℝ}
    (hm0 : 0 ≤ m) (hL0 : 0 ≤ L)
    (hA : A ≤ n) (hn : n ≤ m * (s + 2))
    (hlin : S * S * (m + 2 * m * d + 2 * m * d * d + 2 * m * (s + 2)) ≤
      η ^ 2 / 32 * m ^ 2 * s ^ 2)
    (hquad : 4 * hostC * S * S * (s + 2) * L ≤ η ^ 2 / 32 * s ^ 2) :
    m * S * S + 2 * (m * d + m * d * d + A * (1 + 2 * (hostC * m * L))) * S * S ≤
      (η / 4 * (m * s)) ^ 2 := by
  have hhost0 : 0 ≤ hostC := by norm_num [hostC]
  have hAle : A ≤ m * (s + 2) := hA.trans hn
  have hprod1 : 0 ≤ hostC * m := mul_nonneg hhost0 hm0
  have hprod : 0 ≤ hostC * m * L := mul_nonneg hprod1 hL0
  have hfac : 0 ≤ 1 + 2 * (hostC * m * L) := by nlinarith
  have hAterm : A * (1 + 2 * (hostC * m * L)) ≤
      (m * (s + 2)) * (1 + 2 * (hostC * m * L)) :=
    mul_le_mul_of_nonneg_right hAle hfac
  have hm2nonneg : 0 ≤ m ^ 2 := sq_nonneg m
  have hquad_m := mul_le_mul_of_nonneg_left hquad hm2nonneg
  nlinarith [hlin, hquad_m, hAterm]

lemma eventually_fixed_d_radicand {η : ℝ} (hη0 : 0 < η)
    {s d : ℕ} (hs : 0 < s)
    (hL0 : 0 ≤ Real.log (d : ℝ) / (d : ℝ))
    (hquad :
      4 * hostC * (((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ)) * ((s : ℝ) + 2) *
          (Real.log (d : ℝ) / (d : ℝ)) ≤
        η ^ 2 / 32 * (s : ℝ) ^ 2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ A : ℕ, (A : ℝ) < (n : ℝ) →
        let m := n / (s + 1)
        let S : ℝ := ((s + 1 : ℕ) : ℝ)
        let B : ℝ :=
          (m : ℝ) * (d : ℝ) + (m : ℝ) * (d : ℝ) * (d : ℝ) +
            (A : ℝ) * (1 + 2 * (hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ)))
        (m : ℝ) * S * S + 2 * B * S * S ≤ (η / 4 * ((m * s : ℕ) : ℝ)) ^ 2 := by
  let S : ℝ := ((s + 1 : ℕ) : ℝ)
  let C : ℝ := S * S * (1 + 2 * (d : ℝ) + 2 * (d : ℝ) * (d : ℝ) + 2 * ((s : ℝ) + 2))
  let den : ℝ := η ^ 2 / 32 * (s : ℝ) ^ 2
  have hden_pos : 0 < den := by
    dsimp [den]
    positivity
  let M : ℕ := Nat.ceil (C / den)
  have hMceil : C / den ≤ (M : ℝ) := by
    dsimp [M]
    exact Nat.le_ceil _
  have hCleM : C ≤ den * (M : ℝ) := by
    have htmp := (div_le_iff₀ hden_pos).mp hMceil
    nlinarith
  filter_upwards [eventually_atTop_div_succ (s := s) (P := fun m => M ≤ m)
      (Filter.eventually_ge_atTop M), eventually_mod_succ_le_div_succ s] with n hmM hqle
  intro A hA
  let m := n / (s + 1)
  let q := n % (s + 1)
  let L : ℝ := Real.log (d : ℝ) / (d : ℝ)
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hMle_real : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmM
  have hCle : C ≤ den * (m : ℝ) := by
    exact hCleM.trans (mul_le_mul_of_nonneg_left hMle_real hden_pos.le)
  have hlin0 : C * (m : ℝ) ≤ den * (m : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hCle hm0
    nlinarith
  have hlin : S * S * ((m : ℝ) + 2 * (m : ℝ) * (d : ℝ) +
      2 * (m : ℝ) * (d : ℝ) * (d : ℝ) + 2 * (m : ℝ) * ((s : ℝ) + 2)) ≤
      η ^ 2 / 32 * (m : ℝ) ^ 2 * (s : ℝ) ^ 2 := by
    have hleft : S * S * ((m : ℝ) + 2 * (m : ℝ) * (d : ℝ) +
        2 * (m : ℝ) * (d : ℝ) * (d : ℝ) + 2 * (m : ℝ) * ((s : ℝ) + 2)) =
        C * (m : ℝ) := by
      dsimp [C]
      ring
    have hright : den * (m : ℝ) ^ 2 = η ^ 2 / 32 * (m : ℝ) ^ 2 * (s : ℝ) ^ 2 := by
      dsimp [den]
      ring
    rw [hleft, ← hright]
    exact hlin0
  have hn : n = m * (s + 1) + q := by
    simpa [m, q, Nat.mul_comm] using (Nat.div_add_mod n (s + 1)).symm
  have hnle_nat : n ≤ m * (s + 2) := by
    calc
      n = m * (s + 1) + q := hn
      _ ≤ m * (s + 1) + m := Nat.add_le_add_left hqle _
      _ = m * (s + 2) := by ring
  have hnle : (n : ℝ) ≤ (m : ℝ) * ((s : ℝ) + 2) := by exact_mod_cast hnle_nat
  have hA_le : (A : ℝ) ≤ (n : ℝ) := le_of_lt hA
  have hmain := radicand_bound_real (η := η) (m := (m : ℝ)) (n := (n : ℝ))
    (A := (A : ℝ)) (S := S) (s := (s : ℝ)) (d := (d : ℝ)) (L := L)
    hm0 hL0 hA_le hnle hlin
    (by simpa [S, L, mul_assoc, mul_left_comm, mul_comm] using hquad)
  simpa [m, S, L, Nat.cast_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    using hmain

/-- The pendant-component accounting theorem.

This packages the pendant construction, Lemmas 1-3, and the final numerical assembly from the
write-up.  Its only graph-existence input is Lemma E's eventual host-graph family. -/
theorem pendant_core_counterexamples_from_hosts
    (hHosts : ∀ᶠ d : ℕ in Filter.atTop,
      ∀ᶠ m : ℕ in Filter.atTop,
        ∃ H : SimpleGraph (Fin m), HostGraph d m H) :
    ∀ {η : ℝ}, 0 < η → η < 1 →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ (G : SimpleGraph (Fin n)) (mhr : ℕ),
          G.Connected ∧
            G.CliqueFree 3 ∧
              IsHR 4 G mhr ∧
                (1 - η) * (n : ℝ) ≤ (mhr : ℝ) := by
  intro η hη0 hη1
  rcases exists_nat_pos_eta_mul_add_two_ge_four hη0 with ⟨s, hs, hsη⟩
  let S : ℝ := ((s + 1 : ℕ) : ℝ)
  let target : ℝ := η ^ 2 / 32 * (s : ℝ) ^ 2
  let denom : ℝ := 4 * hostC * (S * S) * ((s : ℝ) + 2)
  have htarget_pos : 0 < target := by
    dsimp [target]
    positivity
  have hdenom_pos : 0 < denom := by
    dsimp [denom, S, hostC]
    positivity
  let ε : ℝ := target / denom
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hD : ∀ᶠ d : ℕ in Filter.atTop,
      (∀ᶠ m : ℕ in Filter.atTop, ∃ H : SimpleGraph (Fin m), HostGraph d m H) ∧
        Real.log (d : ℝ) / (d : ℝ) ≤ ε ∧ 1 ≤ d := by
    filter_upwards [hHosts, eventually_log_div_nat_le hε, Filter.eventually_ge_atTop 1] with
      d hHostD hlogD hd1
    exact ⟨hHostD, hlogD, hd1⟩
  rcases Filter.eventually_atTop.1 hD with ⟨D, hDtail⟩
  let d := D
  rcases hDtail d le_rfl with ⟨hHostD, hlogD, hd1⟩
  have hL0 : 0 ≤ Real.log (d : ℝ) / (d : ℝ) := by
    have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
    have hlog0 : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd1)
    exact div_nonneg hlog0 hdpos.le
  have hdenom_eps : denom * ε = target := by
    dsimp [ε]
    field_simp [hdenom_pos.ne']
  have hquad :
      4 * hostC * (((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ)) * ((s : ℝ) + 2) *
          (Real.log (d : ℝ) / (d : ℝ)) ≤
        η ^ 2 / 32 * (s : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hlogD hdenom_pos.le
    have hmul' : denom * (Real.log (d : ℝ) / (d : ℝ)) ≤ target := by
      nlinarith [hmul, hdenom_eps]
    simpa [denom, S, target, mul_assoc, mul_left_comm, mul_comm] using hmul'
  exact counterexample_family_from_fixed_d_data hη0 hη1 hs hsη hHostD
    (eventually_fixed_d_radicand hη0 hs hL0 hquad)

/-- The asymptotic counterexample family extracted from Lemma E and pendant-core accounting. -/
theorem counterexample_family :
    ∀ {η : ℝ}, 0 < η → η < 1 →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ (G : SimpleGraph (Fin n)) (mhr : ℕ),
          G.Connected ∧
            G.CliqueFree 3 ∧
              IsHR 4 G mhr ∧
                (1 - η) * (n : ℝ) ≤ (mhr : ℝ) := by
  exact pendant_core_counterexamples_from_hosts lemmaE_host_graphs

/-- Convert the asymptotic lower-bound family into the formal negation of the conjecture. -/
theorem erdos_619_solution : erdos_619 := by
  intro hconj
  rcases hconj with ⟨c, hcpos, hc⟩
  set η : ℝ := c / 2
  have hη0 : 0 < η := by positivity
  by_cases hη1 : η < 1
  · rcases (Filter.eventually_atTop.1 (counterexample_family hη0 hη1)) with ⟨n0, hn0⟩
    let n := max n0 1
    rcases hn0 n (le_max_left _ _) with ⟨G, mhr, hGconn, hGtf, hhr, hlower⟩
    have hupper := hc n G mhr hGconn hGtf hhr
    have hηc : 1 - c = 1 - η - η := by ring
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_one) (le_max_right n0 1))
    have hgap : (1 - c) * (n : ℝ) < (1 - η) * (n : ℝ) := by
      rw [hηc]
      nlinarith [mul_pos hη0 hnpos]
    linarith
  · have hcge : 2 ≤ c := by
      dsimp [η] at hη1
      linarith
    rcases (Filter.eventually_atTop.1 (counterexample_family (show (0 : ℝ) < 1 / 2 by norm_num)
        (show (1 / 2 : ℝ) < 1 by norm_num))) with ⟨n0, hn0⟩
    let n := max n0 1
    rcases hn0 n (le_max_left _ _) with ⟨G, mhr, hGconn, hGtf, hhr, _⟩
    have hupper := hc n G mhr hGconn hGtf hhr
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_one) (le_max_right n0 1))
    have : (1 - c) * (n : ℝ) < 0 := by nlinarith
    have hmhr_nonneg : 0 ≤ (mhr : ℝ) := by positivity
    linarith

end

/-- The two repositories' edge-counting conventions agree. -/
lemma addedEdgeCount_eq_ncard {n : ℕ} (G H : SimpleGraph (Fin n)) :
    addedEdgeCount G H = ((H \ G).edgeSet).ncard := by
  rw [edgeSet_sdiff, ← coe_edgeFinset H, ← coe_edgeFinset G, ← Finset.coe_sdiff,
    Set.ncard_coe_finset, addedEdgeCount]

/-- If `m` satisfies the `IsHR r G` predicate, then it equals the formal-conjectures
quantity `Erdos619.minNewEdges r G`. -/
lemma IsHR.minNewEdges_eq {n r m : ℕ} {G : SimpleGraph (Fin n)} (h : IsHR r G m) :
    Erdos619.minNewEdges r G = m := by
  obtain ⟨H, hle, hfree, hdiam, hcount, hmin⟩ := h
  have hmem : m ∈ {k | ∃ H' : SimpleGraph (Fin n),
      G ≤ H' ∧ H'.CliqueFree 3 ∧ H'.ediam ≤ (r : ℕ∞) ∧ ((H' \ G).edgeSet).ncard = k} :=
    ⟨H, hle, hfree, hdiam, by rw [← addedEdgeCount_eq_ncard]; exact hcount⟩
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨m, hmem⟩ ?_)
  rintro k ⟨K, hKle, hKfree, hKdiam, rfl⟩
  rw [← addedEdgeCount_eq_ncard]
  exact hmin K hKle hKfree hKdiam

/-- The formal-conjectures conjecture (the right-hand side of
`Erdos619.erdos_619_solved_statement`) implies this repository's
`erdos_619_conjecture`: specialise the vertex type to `Fin n` and convert the `IsHR`
hypothesis via `IsHR.minNewEdges_eq`. -/
lemma erdos_619_conjecture_of_fc
    (hfc : ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      G.Connected → G.CliqueFree 3 →
      (Erdos619.minNewEdges 4 G : ℝ) < (1 - c) * Fintype.card V) :
    erdos_619_conjecture := by
  obtain ⟨c, hc, hbound⟩ := hfc
  refine ⟨c, hc, fun n G m hconn hfree hm => ?_⟩
  have h := hbound (Fin n) G hconn hfree
  rw [hm.minNewEdges_eq, Fintype.card_fin] at h
  exact h

end Disproof

set_option linter.style.category_attribute true
set_option linter.style.ams_attribute true

/--
**Erdős Problem 619** [EGR98, Er99]: For a triangle-free graph $G$ let $h_r(G)$ be the
smallest number of edges that need to be added to $G$ so that it has diameter $r$ (while
preserving the property of being triangle-free). Is it true that there exists a constant
$c>0$ such that if $G$ is a connected graph on $n$ vertices then $h_4(G)<(1-c)n$?

The answer is **no**: for every $\eta>0$ there exist connected triangle-free graphs on
$n$ vertices with $h_4(G)\geq(1-\eta)n$, so no such constant $c$ exists. The original proof
was generated by Claude Fable 5; the Lean formalization was sketched by Fable and
implemented by GPT 5.5 with Codex.
-/
@[category research solved, AMS 5]
theorem erdos_619 : answer(False) ↔
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      G.Connected → G.CliqueFree 3 →
      (minNewEdges 4 G : ℝ) < (1 - c) * Fintype.card V := by
  exact iff_of_false id fun hfc =>
    Disproof.erdos_619_solution
      (Disproof.erdos_619_conjecture_of_fc hfc)

/-
## Partial results
-/

/--
Erdős, Gyárfás and Ruszinkó [EGR98]: every connected triangle-free graph on a finite
vertex set can be extended, by adding edges, to a triangle-free graph of diameter at
most $3$. This shows that the infimum defining `minNewEdges r G` ranges over a nonempty
set for every `3 ≤ r`.
-/
@[category research solved, AMS 5]
theorem erdos_619.variants.add_edges_diam_three {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (hG' : G.CliqueFree 3) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.CliqueFree 3 ∧ H.ediam ≤ 3 := by
  sorry

/--
Erdős, Gyárfás and Ruszinkó [EGR98]: $h_3(G) \leq n$ for every connected triangle-free
graph $G$ on $n$ vertices.
-/
@[category research solved, AMS 5]
theorem erdos_619.variants.h_three_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (hG' : G.CliqueFree 3) :
    minNewEdges 3 G ≤ Fintype.card V := by
  sorry

/--
Erdős, Gyárfás and Ruszinkó [EGR98]: $h_5(G) \leq \frac{n-1}{2}$ for every connected
triangle-free graph $G$ on $n$ vertices.
-/
@[category research solved, AMS 5]
theorem erdos_619.variants.h_five_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (hG' : G.CliqueFree 3) :
    (minNewEdges 5 G : ℝ) ≤ (Fintype.card V - 1) / 2 := by
  sorry

/--
Erdős, Gyárfás and Ruszinkó [EGR98]: there is a constant $c > 0$ such that for every
$n$ there exist connected triangle-free graphs $G$ on $n$ vertices with
$h_3(G) \geq n - c$.
-/
@[category research solved, AMS 5]
theorem erdos_619.variants.h_three_lower :
    ∃ c > (0 : ℝ), ∀ n : ℕ, 0 < n →
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
        Fintype.card V = n ∧ G.Connected ∧ G.CliqueFree 3 ∧
        (n : ℝ) - c ≤ minNewEdges 3 G := by
  sorry

/-
## Sanity checks
-/

/-- A triangle-free graph that already has diameter at most `r` needs no new edges. -/
@[category test, AMS 5]
theorem erdos_619.test.minNewEdges_eq_zero {V : Type*} {r : ℕ} {G : SimpleGraph V}
    (hG : G.CliqueFree 3) (hdiam : G.ediam ≤ r) :
    minNewEdges r G = 0 :=
  Nat.sInf_eq_zero.mpr <| Or.inl ⟨G, le_rfl, hG, hdiam, by simp⟩

/-- The graph with a single vertex is triangle-free and has diameter `0`, so it needs no
new edges to reach diameter at most `4`. -/
@[category test, AMS 5]
theorem erdos_619.test.minNewEdges_singleton :
    minNewEdges 4 (⊥ : SimpleGraph (Fin 1)) = 0 :=
  erdos_619.test.minNewEdges_eq_zero (cliqueFree_bot (by norm_num))
    (by simp [ediam_eq_zero_of_subsingleton])

end Erdos619
