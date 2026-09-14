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

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Set.Card

@[expose] public section

namespace SimpleGraph

/-- Index set for the pair-vertices $z_{ij}$ of Füredi's $H_k$, encoded as ordered pairs $i < j$. -/
abbrev FurediH.Pair (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}

/--
Vertices of Füredi's $H_k$: an apex $x$, spokes $y_1,\ldots,y_k$, and a vertex $z_{ij}$ for each
pair $i < j$.
-/
inductive FurediH.Vertex (k : ℕ) where
  | apex : Vertex k
  | spoke : Fin k → Vertex k
  | pair : FurediH.Pair k → Vertex k

/-- Equivalence identifying vertices of $H_k$ with an apex, $k$ spokes, and $\binom{k}{2}$
pair-vertices. -/
def FurediH.Vertex.equivSum (k : ℕ) :
    FurediH.Vertex k ≃ Unit ⊕ Fin k ⊕ FurediH.Pair k where
  toFun
    | .apex => Sum.inl ⟨⟩
    | .spoke i => Sum.inr (Sum.inl i)
    | .pair p => Sum.inr (Sum.inr p)
  invFun
    | .inl _ => .apex
    | .inr (.inl i) => .spoke i
    | .inr (.inr p) => .pair p
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | _) <;> rfl

@[simp] lemma FurediH.Vertex.equivSum_symm_inl (k : ℕ) (u : Unit) :
    (FurediH.Vertex.equivSum k).symm (.inl u) = .apex := rfl

@[simp] lemma FurediH.Vertex.equivSum_symm_inr_inl (k : ℕ) (i : Fin k) :
    (FurediH.Vertex.equivSum k).symm (.inr (.inl i)) = .spoke i := rfl

@[simp] lemma FurediH.Vertex.equivSum_symm_inr_inr (k : ℕ) (p : FurediH.Pair k) :
    (FurediH.Vertex.equivSum k).symm (.inr (.inr p)) = .pair p := rfl

instance {k : ℕ} : Fintype (FurediH.Vertex k) :=
  Fintype.ofEquiv _ (FurediH.Vertex.equivSum k).symm

instance {k : ℕ} : DecidableEq (FurediH.Vertex k) := fun a b => by
  cases a <;> cases b <;> simp <;> infer_instance

/-- The number of pair-vertices of $H_k$ is $\binom{k}{2}$. -/
@[simp]
theorem FurediH.card_pair (k : ℕ) : Fintype.card (FurediH.Pair k) = Nat.choose k 2 := by
  classical
  simp [FurediH.Pair, Fintype.card_subtype, Fintype.card_product_filter_lt, Fintype.card_fin]

/-- Cardinality of the vertex set of $H_k$: one apex, $k$ spokes, and $\binom{k}{2}$ pair-vertices. -/
@[simp]
theorem FurediH.card_vertex (k : ℕ) :
    Fintype.card (FurediH.Vertex k) = 1 + k + Nat.choose k 2 := by
  rw [Fintype.card_congr (FurediH.Vertex.equivSum k), Fintype.card_sum, Fintype.card_sum,
    Fintype.card_unit, Fintype.card_fin, FurediH.card_pair, Nat.add_assoc]

/--
Adjacency of $H_k$ before `fromRel`: the apex is joined to every $y_i$, and each $z_{ij}$ is joined
to $y_i$ and $y_j$.
-/
def FurediH.adjRel {k : ℕ} : FurediH.Vertex k → FurediH.Vertex k → Prop
  | .apex, .spoke _ => True
  | .spoke a, .pair p => a = p.1.1 ∨ a = p.1.2
  | _, _ => False

instance {k : ℕ} : DecidableRel (FurediH.adjRel (k := k)) := fun a b => by
  cases a <;> cases b <;> dsimp [FurediH.adjRel] <;> infer_instance

/--
Füredi's graph $H_k$: vertices $x,y_1,\ldots,y_k$ and $z_{ij}$ for $i<j$, with $x$ adjacent to every
$y_i$ and each pair $y_i,y_j$ adjacent to the unique vertex $z_{ij}$.
-/
def furediH (k : ℕ) : SimpleGraph (FurediH.Vertex k) :=
  fromRel (FurediH.adjRel (k := k))

instance {k : ℕ} : DecidableRel (furediH k).Adj :=
  inferInstanceAs (DecidableRel (fromRel (FurediH.adjRel (k := k))).Adj)

noncomputable instance {k : ℕ} (v : FurediH.Vertex k) :
    Fintype ((furediH k).neighborSet v) :=
  inferInstance

noncomputable instance {k : ℕ} : Fintype (furediH k).edgeSet :=
  inferInstance

/-- The apex is adjacent to every spoke. -/
lemma furediH_adj_apex_spoke {k : ℕ} (i : Fin k) :
    (furediH k).Adj .apex (.spoke i) := by
  simp [furediH, SimpleGraph.fromRel_adj, FurediH.adjRel]

/-- A spoke is adjacent to a pair-vertex precisely when it is one of the pair's endpoints. -/
lemma furediH_adj_spoke_pair {k : ℕ} {i : Fin k} {p : FurediH.Pair k}
    (h : i = p.1.1 ∨ i = p.1.2) :
    (furediH k).Adj (.spoke i) (.pair p) := by
  simp [furediH, SimpleGraph.fromRel_adj, FurediH.adjRel, h]

/-- The apex is never adjacent to a pair-vertex. -/
lemma not_furediH_adj_apex_pair {k : ℕ} (p : FurediH.Pair k) :
    ¬ (furediH k).Adj .apex (.pair p) := by
  simp [furediH, SimpleGraph.fromRel_adj, FurediH.adjRel]

/-- Distinct spokes are never adjacent (the $y_i$ form an independent set). -/
lemma not_furediH_adj_spoke_spoke {k : ℕ} (i j : Fin k) :
    ¬ (furediH k).Adj (.spoke i) (.spoke j) := by
  simp [furediH, SimpleGraph.fromRel_adj, FurediH.adjRel]

/-- Pair-vertices are never adjacent to each other. -/
lemma not_furediH_adj_pair_pair {k : ℕ} (p q : FurediH.Pair k) :
    ¬ (furediH k).Adj (.pair p) (.pair q) := by
  simp [furediH, SimpleGraph.fromRel_adj, FurediH.adjRel]

/-- Spoke–pair adjacency is exactly the endpoint condition. -/
lemma furediH_adj_spoke_pair_iff {k : ℕ} {i : Fin k} {p : FurediH.Pair k} :
    (furediH k).Adj (.spoke i) (.pair p) ↔ i = p.1.1 ∨ i = p.1.2 := by
  simp [furediH, SimpleGraph.fromRel_adj, FurediH.adjRel]

/-- The spoke vertices form an independent set. -/
lemma furediH_isIndepSet_spokes (k : ℕ) :
    (furediH k).IsIndepSet (Set.range (FurediH.Vertex.spoke (k := k))) := by
  intro x hx y hy _ hadj
  obtain ⟨i, rfl⟩ := Set.mem_range.mp hx
  obtain ⟨j, rfl⟩ := Set.mem_range.mp hy
  exact not_furediH_adj_spoke_spoke i j hadj

/-- The pair-vertices form an independent set. -/
lemma furediH_isIndepSet_pairs (k : ℕ) :
    (furediH k).IsIndepSet (Set.range (FurediH.Vertex.pair (k := k))) := by
  intro x hx y hy _ hadj
  obtain ⟨p, rfl⟩ := Set.mem_range.mp hx
  obtain ⟨q, rfl⟩ := Set.mem_range.mp hy
  exact not_furediH_adj_pair_pair p q hadj

/-- Neighbours of the apex are exactly the spokes. -/
lemma furediH_neighborSet_apex (k : ℕ) :
    (furediH k).neighborSet .apex = Set.range (FurediH.Vertex.spoke (k := k)) := by
  ext v
  cases v with
  | apex =>
      simp [mem_neighborSet, SimpleGraph.irrefl]
  | spoke i =>
      simp [mem_neighborSet, furediH_adj_apex_spoke]
  | pair p =>
      simp [mem_neighborSet, not_furediH_adj_apex_pair]

/-- The apex has exactly `k` neighbours (the spokes). -/
lemma furediH_ncard_neighborSet_apex (k : ℕ) :
    ((furediH k).neighborSet .apex).ncard = k := by
  rw [furediH_neighborSet_apex,
    Set.ncard_range_of_injective (fun _ _ h ↦ FurediH.Vertex.spoke.inj h)]
  simp [Nat.card_eq_fintype_card]

/-- Each spoke is adjacent to the apex. -/
lemma furediH_adj_spoke_apex {k : ℕ} (i : Fin k) :
    (furediH k).Adj (.spoke i) .apex :=
  (furediH_adj_apex_spoke i).symm

/-- Neighbours of a spoke: the apex and the pair-vertices incident to that spoke. -/
lemma furediH_neighborSet_spoke {k : ℕ} (i : Fin k) :
    (furediH k).neighborSet (.spoke i) =
      {FurediH.Vertex.apex} ∪
        FurediH.Vertex.pair '' {p : FurediH.Pair k | i = p.1.1 ∨ i = p.1.2} := by
  ext v
  cases v with
  | apex =>
      simp [mem_neighborSet, furediH_adj_spoke_apex]
  | spoke j =>
      simp [mem_neighborSet, not_furediH_adj_spoke_spoke]
  | pair p =>
      simp [mem_neighborSet, furediH_adj_spoke_pair_iff, Set.mem_image]

/-- Neighbours of a pair-vertex are exactly its two endpoint spokes. -/
lemma furediH_neighborSet_pair {k : ℕ} (p : FurediH.Pair k) :
    (furediH k).neighborSet (.pair p) =
      {FurediH.Vertex.spoke p.1.1, .spoke p.1.2} := by
  ext v
  cases v with
  | apex =>
      have : ¬ (furediH k).Adj (.pair p) .apex := fun h ↦
        not_furediH_adj_apex_pair p h.symm
      simp [mem_neighborSet, this]
  | spoke i =>
      simp [mem_neighborSet, (furediH k).adj_comm (.pair p) (.spoke i),
        furediH_adj_spoke_pair_iff]
  | pair q =>
      simp [mem_neighborSet, not_furediH_adj_pair_pair]

/-- Each pair-vertex has exactly two neighbours. -/
lemma furediH_ncard_neighborSet_pair {k : ℕ} (p : FurediH.Pair k) :
    ((furediH k).neighborSet (.pair p)).ncard = 2 := by
  rw [furediH_neighborSet_pair]
  have hne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  have : FurediH.Vertex.spoke p.1.1 ∉ ({FurediH.Vertex.spoke p.1.2} : Set _) := by
    simp [hne]
  rw [Set.ncard_insert_of_notMem this, Set.ncard_singleton]

/-- There are exactly `k - 1` pair-vertices incident to a fixed spoke. -/
lemma furediH_ncard_pairs_incident {k : ℕ} (i : Fin k) :
    ({p : FurediH.Pair k | i = p.1.1 ∨ i = p.1.2}).ncard = k - 1 := by
  classical
  set S := (Finset.univ : Finset (FurediH.Pair k)).filter
    fun p => i = p.1.1 ∨ i = p.1.2
  have hS : ({p : FurediH.Pair k | i = p.1.1 ∨ i = p.1.2}).toFinset = S := by
    ext; simp [S]
  rw [Set.ncard_eq_toFinset_card', hS]
  set Sfst := (Finset.univ : Finset (FurediH.Pair k)).filter fun p => i = p.1.1
  set Ssnd := (Finset.univ : Finset (FurediH.Pair k)).filter fun p => i = p.1.2
  have hdisj : Disjoint Sfst Ssnd := by
    refine Finset.disjoint_left.2 fun p hp1 hp2 => ?_
    have h1 := (Finset.mem_filter.mp hp1).2
    have h2 := (Finset.mem_filter.mp hp2).2
    exact (ne_of_lt p.2) (h1.symm.trans h2)
  have hunion : S = Sfst ∪ Ssnd := by
    ext p; simp [S, Sfst, Ssnd]
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  have c1 : Sfst.card = (Finset.Ioi i).card := by
    refine Finset.card_bij (fun p _ => p.1.2) ?_ ?_ ?_
    · intro p hp
      have hp' : i = p.1.1 := (Finset.mem_filter.mp hp).2
      exact Finset.mem_Ioi.mpr (hp' ▸ p.2)
    · intro p hp q hq h
      have hp' := (Finset.mem_filter.mp hp).2
      have hq' := (Finset.mem_filter.mp hq).2
      exact Subtype.ext (Prod.ext (hp'.symm.trans hq') h)
    · intro j hj
      refine ⟨⟨(i, j), Finset.mem_Ioi.mp hj⟩, by simp [Sfst], rfl⟩
  have c2 : Ssnd.card = (Finset.Iio i).card := by
    refine Finset.card_bij (fun p _ => p.1.1) ?_ ?_ ?_
    · intro p hp
      have hp' : i = p.1.2 := (Finset.mem_filter.mp hp).2
      exact Finset.mem_Iio.mpr (by simpa [hp'] using p.2)
    · intro p hp q hq h
      have hp' := (Finset.mem_filter.mp hp).2
      have hq' := (Finset.mem_filter.mp hq).2
      exact Subtype.ext (Prod.ext h (hp'.symm.trans hq'))
    · intro j hj
      refine ⟨⟨(j, i), Finset.mem_Iio.mp hj⟩, by simp [Ssnd], rfl⟩
  rw [c1, c2, Fin.card_Ioi, Fin.card_Iio]
  omega

/-- Each spoke has exactly `k` neighbours (apex + `k - 1` incident pairs). -/
lemma furediH_ncard_neighborSet_spoke {k : ℕ} (i : Fin k) :
    ((furediH k).neighborSet (.spoke i)).ncard = k := by
  classical
  rw [furediH_neighborSet_spoke]
  have hdisj :
      Disjoint ({FurediH.Vertex.apex} : Set _)
        (FurediH.Vertex.pair '' {p : FurediH.Pair k | i = p.1.1 ∨ i = p.1.2}) := by
    refine Set.disjoint_left.2 fun _ hx hx' => ?_
    obtain ⟨_, _, rfl⟩ := hx'
    simp at hx
  have hinj : Function.Injective (FurediH.Vertex.pair (k := k)) :=
    fun _ _ h => FurediH.Vertex.pair.inj h
  rw [Set.ncard_union_eq hdisj, Set.ncard_singleton,
    Set.ncard_image_of_injective _ hinj, furediH_ncard_pairs_incident]
  have : (i : ℕ) < k := i.isLt
  omega

lemma furediH_degree_eq_ncard_neighborSet {k : ℕ} (v : FurediH.Vertex k) :
    (furediH k).degree v = ((furediH k).neighborSet v).ncard := by
  simp [degree, neighborFinset_def, Set.ncard_eq_toFinset_card']

lemma furediH_degree_apex (k : ℕ) : (furediH k).degree .apex = k := by
  rw [furediH_degree_eq_ncard_neighborSet, furediH_ncard_neighborSet_apex]

lemma furediH_degree_spoke {k : ℕ} (i : Fin k) :
    (furediH k).degree (.spoke i) = k := by
  rw [furediH_degree_eq_ncard_neighborSet, furediH_ncard_neighborSet_spoke]

lemma furediH_degree_pair {k : ℕ} (p : FurediH.Pair k) :
    (furediH k).degree (.pair p) = 2 := by
  rw [furediH_degree_eq_ncard_neighborSet, furediH_ncard_neighborSet_pair]

lemma two_mul_choose_two (k : ℕ) : 2 * Nat.choose k 2 = k * (k - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self k))

/-- $H_k$ has exactly $k^2$ edges. -/
theorem furediH_card_edgeFinset (k : ℕ) : (furediH k).edgeFinset.card = k ^ 2 := by
  classical
  have hsum :
      ∑ v : FurediH.Vertex k, ((furediH k).neighborSet v).ncard =
        2 * (furediH k).edgeFinset.card := by
    simpa [furediH_degree_eq_ncard_neighborSet] using
      (furediH k).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_equiv (FurediH.Vertex.equivSum k)
      (fun v => ((furediH k).neighborSet v).ncard)
      (fun x => ((furediH k).neighborSet ((FurediH.Vertex.equivSum k).symm x)).ncard)
      (fun v => by rw [Equiv.symm_apply_apply])] at hsum
  simp only [Fintype.sum_sum_type, FurediH.Vertex.equivSum_symm_inl,
    FurediH.Vertex.equivSum_symm_inr_inl, FurediH.Vertex.equivSum_symm_inr_inr] at hsum
  simp_rw [furediH_ncard_neighborSet_apex, furediH_ncard_neighborSet_spoke,
    furediH_ncard_neighborSet_pair] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_punit, Fintype.card_fin,
    FurediH.card_pair, nsmul_eq_mul, Nat.cast_id] at hsum
  rw [show Nat.choose k 2 * 2 = k * (k - 1) from
    (mul_comm _ _).trans (two_mul_choose_two k)] at hsum
  -- hsum : k + (k * k + k * (k - 1)) = 2 * #edges
  have hk : ∀ n, n + n * (n - 1) = n * n := by
    intro n
    cases n with
    | zero => rfl
    | succ n =>
      change n + 1 + (n + 1) * n = (n + 1) * (n + 1)
      rw [add_comm (n + 1), ← Nat.mul_succ]
  have hpow : k + (k * k + k * (k - 1)) = 2 * k ^ 2 := by
    rw [← add_assoc, add_comm k (k * k), add_assoc, hk k, pow_two, two_mul]
  omega




/-- Apex together with all pair-vertices form an independent set. -/
lemma furediH_isIndepSet_apex_pairs (k : ℕ) :
    (furediH k).IsIndepSet ({FurediH.Vertex.apex} ∪ Set.range (FurediH.Vertex.pair (k := k))) := by
  intro x hx y hy hxy hadj
  cases hx with
  | inl hx =>
    cases hy with
    | inl hy => exact hxy (hx.trans hy.symm)
    | inr hy =>
      obtain ⟨p, rfl⟩ := Set.mem_range.mp hy
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact not_furediH_adj_apex_pair p hadj
  | inr hx =>
    cases hy with
    | inl hy =>
      obtain ⟨p, rfl⟩ := Set.mem_range.mp hx
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact not_furediH_adj_apex_pair p hadj.symm
    | inr hy =>
      obtain ⟨p, rfl⟩ := Set.mem_range.mp hx
      obtain ⟨q, rfl⟩ := Set.mem_range.mp hy
      exact not_furediH_adj_pair_pair p q hadj

/-- $H_k$ is triangle-free. -/
theorem furediH_cliqueFree_three (k : ℕ) : (furediH k).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs.card_eq
  have hab' : (furediH k).Adj a b := hs.isClique (by simp) (by simp) hab
  have hac' : (furediH k).Adj a c := hs.isClique (by simp) (by simp) hac
  have hbc' : (furediH k).Adj b c := hs.isClique (by simp) (by simp) hbc
  cases a <;> cases b <;> cases c <;>
    simp [furediH, SimpleGraph.fromRel_adj, FurediH.adjRel] at hab' hac' hbc'

/-- Explicit $C_4$ copy in $H_k$ for $k \ge 2$: spoke $0$, apex, spoke $1$, pair $\{0,1\}$. -/
noncomputable def furediH.cycle4Copy {k : ℕ} (hk : 2 ≤ k) :
    Copy (cycleGraph 4) (furediH k) := by
  classical
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  have hij : i < j := by simp [i, j]
  let p : FurediH.Pair k := ⟨(i, j), hij⟩
  let f : Fin 4 → FurediH.Vertex k := fun x =>
    match x.val with
    | 0 => FurediH.Vertex.spoke i
    | 1 => FurediH.Vertex.apex
    | 2 => FurediH.Vertex.spoke j
    | _ => FurediH.Vertex.pair p
  refine Hom.toCopy ⟨f, ?_⟩ ?_
  · intro a b hab
    -- Order of `fin_cases a <;> fin_cases b` is row-major on `{0,1,2,3}²`.
    fin_cases a <;> fin_cases b
    · exact (hab.ne rfl).elim
    · simpa [f] using furediH_adj_spoke_apex i
    · have : ¬(cycleGraph 4).Adj (0 : Fin 4) 2 := by decide
      exact (this hab).elim
    · simpa [f] using furediH_adj_spoke_pair (p := p) (Or.inl rfl)
    · simpa [f] using (furediH_adj_spoke_apex i).symm
    · exact (hab.ne rfl).elim
    · simpa [f] using furediH_adj_apex_spoke j
    · have : ¬(cycleGraph 4).Adj (1 : Fin 4) 3 := by decide
      exact (this hab).elim
    · have : ¬(cycleGraph 4).Adj (2 : Fin 4) 0 := by decide
      exact (this hab).elim
    · simpa [f] using (furediH_adj_apex_spoke j).symm
    · exact (hab.ne rfl).elim
    · simpa [f] using furediH_adj_spoke_pair (p := p) (Or.inr rfl)
    · simpa [f] using (furediH_adj_spoke_pair (p := p) (Or.inl rfl)).symm
    · have : ¬(cycleGraph 4).Adj (3 : Fin 4) 1 := by decide
      exact (this hab).elim
    · simpa [f] using (furediH_adj_spoke_pair (p := p) (Or.inr rfl)).symm
    · exact (hab.ne rfl).elim
  · intro a b h
    fin_cases a <;> fin_cases b
    · rfl
    · cases h
    · exact absurd (FurediH.Vertex.spoke.inj h) (by simp [i, j] : i ≠ j)
    · cases h
    · cases h
    · rfl
    · cases h
    · cases h
    · exact absurd (FurediH.Vertex.spoke.inj h).symm (by simp [i, j] : i ≠ j)
    · cases h
    · rfl
    · cases h
    · cases h
    · cases h
    · cases h
    · rfl

/-- For $k \ge 2$, Füredi's $H_k$ contains a $4$-cycle (supports the $\mathrm{ex}\gg n^{3/2}$ lower bound). -/
theorem furediH_contains_cycleGraph_four {k : ℕ} (hk : 2 ≤ k) :
    cycleGraph 4 ⊑ furediH k :=
  ⟨furediH.cycle4Copy hk⟩


/-- Every vertex of $H_k$ is reachable from the apex. -/
lemma furediH_reachable_apex (k : ℕ) (v : FurediH.Vertex k) :
    (furediH k).Reachable .apex v := by
  cases v with
  | apex => exact Reachable.rfl
  | spoke i => exact (furediH_adj_apex_spoke i).reachable
  | pair p =>
    exact (furediH_adj_apex_spoke p.1.1).reachable.trans
      (furediH_adj_spoke_pair (Or.inl rfl)).reachable

/-- $H_k$ is preconnected (hence path-connected between any two vertices). -/
lemma furediH_preconnected (k : ℕ) : (furediH k).Preconnected :=
  fun u v => (furediH_reachable_apex k u).symm.trans (furediH_reachable_apex k v)

/-- $H_k$ is connected. -/
theorem furediH_connected (k : ℕ) : (furediH k).Connected :=
  haveI : Nonempty (FurediH.Vertex k) := ⟨.apex⟩
  ⟨furediH_preconnected k⟩



/-- Left part of the natural bipartition: apex and all pair-vertices. -/
def furediH.partLeft (k : ℕ) : Set (FurediH.Vertex k) :=
  {v | ∀ i : Fin k, v ≠ .spoke i}

/-- Right part: the spoke-vertices `y_i`. -/
def furediH.partRight (k : ℕ) : Set (FurediH.Vertex k) :=
  {v | ∃ i : Fin k, v = .spoke i}

@[simp] lemma furediH.apex_mem_partLeft (k : ℕ) :
    (FurediH.Vertex.apex : FurediH.Vertex k) ∈ furediH.partLeft k := by
  intro i; simp

@[simp] lemma furediH.pair_mem_partLeft {k : ℕ} (p : FurediH.Pair k) :
    FurediH.Vertex.pair p ∈ furediH.partLeft k := by
  intro i; simp

@[simp] lemma furediH.spoke_mem_partRight {k : ℕ} (i : Fin k) :
    FurediH.Vertex.spoke i ∈ furediH.partRight k :=
  ⟨i, rfl⟩

@[simp] lemma furediH.spoke_not_mem_partLeft {k : ℕ} (i : Fin k) :
    FurediH.Vertex.spoke i ∉ furediH.partLeft k := by
  intro h; exact (h i) rfl

/-- $H_k$ is bipartite with parts `{apex} ∪ \{z_{ij}\}$ and `{y_1,…,y_k}`. -/
lemma furediH_isBipartiteWith (k : ℕ) :
    (furediH k).IsBipartiteWith (furediH.partLeft k) (furediH.partRight k) where
  disjoint := by
    rw [Set.disjoint_left]
    intro v hvL hvR
    obtain ⟨i, rfl⟩ := hvR
    exact furediH.spoke_not_mem_partLeft i hvL
  mem_of_adj := by
    intro v w hadj
    cases v with
    | apex =>
      cases w with
      | apex =>
        simp [furediH] at hadj
      | spoke i =>
        exact Or.inl ⟨furediH.apex_mem_partLeft k, furediH.spoke_mem_partRight i⟩
      | pair p =>
        exact (not_furediH_adj_apex_pair p hadj).elim
    | spoke i =>
      cases w with
      | apex =>
        exact Or.inr ⟨furediH.spoke_mem_partRight i, furediH.apex_mem_partLeft k⟩
      | spoke j =>
        exact (not_furediH_adj_spoke_spoke i j hadj).elim
      | pair p =>
        exact Or.inr ⟨furediH.spoke_mem_partRight i, furediH.pair_mem_partLeft p⟩
    | pair p =>
      cases w with
      | apex =>
        exact (not_furediH_adj_apex_pair p hadj.symm).elim
      | spoke i =>
        exact Or.inl ⟨furediH.pair_mem_partLeft p, furediH.spoke_mem_partRight i⟩
      | pair q =>
        exact (not_furediH_adj_pair_pair p q hadj).elim

/-- Hence $H_k$ is bipartite (2-colorable). -/
theorem furediH_isBipartite (k : ℕ) : (furediH k).IsBipartite :=
  isBipartite_iff_exists_isBipartiteWith.mpr ⟨_, _, furediH_isBipartiteWith k⟩

/-- In particular the chromatic number is at most `2`. -/
theorem furediH_chromaticNumber_le_two (k : ℕ) :
    (furediH k).chromaticNumber ≤ 2 :=
  chromaticNumber_le_two_iff_isBipartite.mpr (furediH_isBipartite k)


end SimpleGraph
