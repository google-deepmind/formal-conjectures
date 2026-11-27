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
# The Alon–Saks–Seymour conjecture (disproved)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Graham%E2%80%93Pollak_theorem)
* [GP71] Graham, R. L. and Pollak, H. O. (1971). "On the addressing problem for loop switching."
  *Bell System Tech. J.* 50, pp. 2495--2519.
* [Ka91] Kahn, J. (1991). "Recent results on some not-so-recent hypergraph matching and covering
  problems." *Extremal problems for finite sets (Visegrád)*, Bolyai Soc. Math. Stud. 3,
  pp. 305--353.
* [HS12] Huang, H. and Sudakov, B. (2012). "A counterexample to the Alon–Saks–Seymour
  conjecture and related problems." *Combinatorica* 32, pp. 205--219.
  [arXiv:1002.4687](https://arxiv.org/abs/1002.4687)
-/

@[expose] public section

open SimpleGraph Finset

namespace AlonSaksSeymourConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Membership of the (unordered) pair `u, v` in the biclique with sides `A` and `B`. -/
def InBiclique (A B : Finset V) (u v : V) : Prop :=
  (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)

/-- A family of `k` bicliques with sides `A i`, `B i` is a **biclique partition** of `G` if the
sides are disjoint and every edge of `G` lies in exactly one of the bicliques (and every
biclique pair is an edge of `G`). -/
structure IsBicliquePartition (G : SimpleGraph V) (k : ℕ) (A B : Fin k → Finset V) : Prop where
  disjoint : ∀ i, Disjoint (A i) (B i)
  adj_iff : ∀ u v, G.Adj u v ↔ ∃ i, InBiclique (A i) (B i) u v
  unique : ∀ u v i j, InBiclique (A i) (B i) u v → InBiclique (A j) (B j) u v → i = j

/-- The **biclique partition number** `bp(G)`: the least number of edge-disjoint complete
bipartite subgraphs whose edge sets partition `E(G)`. -/
noncomputable def bicliquePartitionNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ A B : Fin k → Finset V, IsBicliquePartition G k A B}

/--
**The Alon–Saks–Seymour conjecture — disproved.**

It was conjectured (Alon, Saks and Seymour, c. 1991, see [Ka91]) that every graph whose edge
set is partitioned into $k$ complete bipartite subgraphs is $(k+1)$-colourable, i.e.
$\chi(G) \le \operatorname{bp}(G) + 1$ — the natural generalisation of the Graham–Pollak
theorem, which is the case $G = K_n$.

This is **false**: Huang and Sudakov [HS12] constructed graphs with
$\chi(G) \ge c \operatorname{bp}(G)^{6/5}$.
-/
@[category research solved, AMS 5]
theorem alon_saks_seymour_conjecture : ¬
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.chromaticNumber ≤ bicliquePartitionNumber G + 1 := by
  sorry

/-- The stars centred at `0, 1, …, n - 2` partition the edges of `K_n`. -/
@[category API, AMS 5]
lemma isBicliquePartition_stars (n : ℕ) :
    IsBicliquePartition (completeGraph (Fin n)) (n - 1)
      (fun i => {u | u.val = i.val}) (fun i => {u | i.val < u.val}) where
  disjoint i := by
    rw [Finset.disjoint_left]
    intro u h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    omega
  adj_iff u v := by
    simp only [completeGraph, top_adj, InBiclique, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro huv
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne huv) with h | h
      · exact ⟨⟨u.val, by omega⟩, Or.inl ⟨rfl, h⟩⟩
      · exact ⟨⟨v.val, by omega⟩, Or.inr ⟨h, rfl⟩⟩
    · rintro ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ h <;> subst h <;> omega
  unique u v i j := by
    simp only [InBiclique, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) (⟨h3, h4⟩ | ⟨h3, h4⟩) <;> ext <;> omega

/-- Tverberg's argument: a biclique partition of the complete graph on `V` has at least
`|V| - 1` parts. -/
@[category API, AMS 5]
lemma card_le_of_isBicliquePartition {k : ℕ} {A B : Fin k → Finset V}
    (h : IsBicliquePartition (completeGraph V) k A B) : Fintype.card V ≤ k + 1 := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  let M : Matrix (Option (Fin k)) V ℝ := fun o u => o.elim 1 fun m => if u ∈ A m then 1 else 0
  have hker : (Matrix.mulVecLin M).ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_option, Fintype.card_fin] using hlt)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hker
  have hM : ∀ o, ∑ u, M o u * x u = 0 := fun o => congrFun hx o
  have hsum : ∑ u, x u = 0 := by simpa [M] using hM none
  have hA : ∀ m, ∑ u, (if u ∈ A m then x u else 0) = 0 := fun m => by
    simpa [M, ite_mul] using hM (some m)
  -- each ordered pair of distinct vertices lies in exactly one biclique
  have hind : ∀ u v, (if u ≠ v then (1 : ℝ) else 0) =
      ∑ m, ((if u ∈ A m ∧ v ∈ B m then 1 else 0) + (if u ∈ B m ∧ v ∈ A m then 1 else 0)) := by
    intro u v
    have hm : ∀ m, ((if u ∈ A m ∧ v ∈ B m then (1 : ℝ) else 0) +
        (if u ∈ B m ∧ v ∈ A m then 1 else 0)) = if InBiclique (A m) (B m) u v then 1 else 0 := by
      intro m
      have := Finset.disjoint_left.mp (h.disjoint m)
      unfold InBiclique
      by_cases h1 : u ∈ A m <;> by_cases h2 : v ∈ B m <;> by_cases h3 : u ∈ B m <;>
        by_cases h4 : v ∈ A m <;> simp_all
    simp only [hm, Finset.sum_boole]
    split_ifs with huv
    · obtain ⟨m, hm⟩ := (h.adj_iff u v).mp (by simpa [completeGraph] using huv)
      have : ({m' | InBiclique (A m') (B m') u v} : Finset (Fin k)) = {m} := by
        ext m'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun hm' => h.unique u v m' m hm' hm, fun e => e ▸ hm⟩
      simp [this]
    · have : ∀ m, ¬ InBiclique (A m) (B m) u v := fun m hm =>
        (by simpa [completeGraph] using (h.adj_iff u v).mpr ⟨m, hm⟩ : u ≠ v) (not_not.mp huv)
      simp [this]
  have hcross : ∑ u, ∑ v, (if u ≠ v then (1 : ℝ) else 0) * (x u * x v) = 0 := by
    have hm : ∀ m, ∑ u, ∑ v, ((if u ∈ A m ∧ v ∈ B m then (1 : ℝ) else 0) +
        (if u ∈ B m ∧ v ∈ A m then 1 else 0)) * (x u * x v) = 0 := by
      intro m
      have e : ∀ u v, ((if u ∈ A m ∧ v ∈ B m then (1 : ℝ) else 0) +
          (if u ∈ B m ∧ v ∈ A m then 1 else 0)) * (x u * x v) =
          (if u ∈ A m then x u else 0) * (if v ∈ B m then x v else 0) +
          (if u ∈ B m then x u else 0) * (if v ∈ A m then x v else 0) := by
        intro u v
        by_cases h1 : u ∈ A m <;> by_cases h2 : v ∈ B m <;> by_cases h3 : u ∈ B m <;>
          by_cases h4 : v ∈ A m <;> simp [h1, h2, h3, h4, mul_comm, one_add_one_eq_two, mul_two]
      simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul_sum, hA, zero_mul, mul_zero,
        add_zero]
    calc ∑ u, ∑ v, (if u ≠ v then (1 : ℝ) else 0) * (x u * x v)
        = ∑ u, ∑ v, ∑ m, ((if u ∈ A m ∧ v ∈ B m then (1 : ℝ) else 0) +
            (if u ∈ B m ∧ v ∈ A m then 1 else 0)) * (x u * x v) := by
          simp only [hind, Finset.sum_mul]
      _ = ∑ m, ∑ u, ∑ v, ((if u ∈ A m ∧ v ∈ B m then (1 : ℝ) else 0) +
            (if u ∈ B m ∧ v ∈ A m then 1 else 0)) * (x u * x v) := by
          exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero fun m _ => hm m
  have hsq : ∑ u, x u ^ 2 = 0 := by
    have h2 : (∑ u, x u) * (∑ v, x v) =
        ∑ u, x u ^ 2 + ∑ u, ∑ v, (if u ≠ v then (1 : ℝ) else 0) * (x u * x v) := by
      rw [Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      calc ∑ v, x u * x v
          = ∑ v, ((if u = v then x u * x v else 0) +
              (if u ≠ v then (1 : ℝ) else 0) * (x u * x v)) :=
            Finset.sum_congr rfl fun v _ => by by_cases huv : u = v <;> simp [huv]
        _ = x u ^ 2 + ∑ v, (if u ≠ v then (1 : ℝ) else 0) * (x u * x v) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
          simp [sq]
    rw [hsum, zero_mul, hcross, add_zero] at h2
    exact h2.symm
  apply hx0
  funext u
  have := (Finset.sum_eq_zero_iff_of_nonneg fun u _ => sq_nonneg (x u)).mp hsq u
    (Finset.mem_univ u)
  simpa using this

/--
**The Graham–Pollak theorem (1971).**

The edge set of $K_n$ cannot be partitioned into fewer than $n - 1$ complete bipartite
subgraphs, and $n - 1$ suffice: $\operatorname{bp}(K_n) = n - 1$.

*Reference:* [GP71].
-/
@[category research solved, AMS 5]
theorem alon_saks_seymour_conjecture.variants.graham_pollak (n : ℕ) :
    bicliquePartitionNumber (completeGraph (Fin n)) = n - 1 := by
  unfold bicliquePartitionNumber
  refine le_antisymm (Nat.sInf_le ⟨_, _, isBicliquePartition_stars n⟩) ?_
  have hne : {k | ∃ A B : Fin k → Finset (Fin n),
      IsBicliquePartition (completeGraph (Fin n)) k A B}.Nonempty :=
    ⟨n - 1, _, _, isBicliquePartition_stars n⟩
  obtain ⟨A, B, h⟩ := Nat.sInf_mem hne
  have := card_le_of_isBicliquePartition h
  rw [Fintype.card_fin] at this
  omega

/--
**Huang–Sudakov (2012): a polynomial separation.**

There is a constant $c > 0$ and, for every $k$, a graph $G$ with $\operatorname{bp}(G) \le k$
and $\chi(G) \ge c\,k^{6/5}$.

*Reference:* [HS12].
-/
@[category research solved, AMS 5]
theorem alon_saks_seymour_conjecture.variants.huang_sudakov :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V), bicliquePartitionNumber G ≤ k ∧
        (c * (k : ℝ) ^ ((6 : ℝ) / 5) : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) := by
  sorry

omit [Fintype V] [DecidableEq V] in
/-- The empty family is a biclique partition of the empty graph. -/
@[category API, AMS 5]
lemma isBicliquePartition_bot :
    IsBicliquePartition (⊥ : SimpleGraph V) 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) where
  disjoint i := Fin.elim0 i
  adj_iff u v := by simp
  unique u v i := Fin.elim0 i

omit [Fintype V] [DecidableEq V] in
/-- The empty graph has biclique partition number `0`. -/
@[category API, AMS 5]
lemma bicliquePartitionNumber_bot : bicliquePartitionNumber (⊥ : SimpleGraph V) = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le ⟨_, _, isBicliquePartition_bot⟩)

omit [Fintype V] [DecidableEq V] in
/--
**The conjectured inequality holds for the empty graph.**

The empty graph has `bp = 0` and chromatic number at most `1`, so `χ ≤ bp + 1`.
-/
@[category test, AMS 5]
theorem alon_saks_seymour_conjecture.variants.bot :
    (⊥ : SimpleGraph V).chromaticNumber ≤ bicliquePartitionNumber (⊥ : SimpleGraph V) + 1 := by
  rw [bicliquePartitionNumber_bot, Nat.cast_zero, zero_add]
  exact Colorable.chromaticNumber_le ⟨⟨fun _ => 0, fun h => by simp at h⟩⟩

end AlonSaksSeymourConjecture
