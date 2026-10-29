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
# Erdős Problem 19

The Erdős–Faber–Lovász conjecture: if $G$ is an edge-disjoint union of $n$ copies of $K_n$,
is $\chi(G) = n$?

We model $G$ by a family of $n$ vertex sets of size $n$ (the copies of $K_n$) which pairwise
share at most one vertex and which cover the vertex type. Two copies of $K_n$ are
edge-disjoint exactly when their vertex sets share at most one vertex.

*References:*
* [erdosproblems.com/19](https://www.erdosproblems.com/19)
* [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica 1 (1981), 25-42.
* [Hi81] Hindman, N., *On a conjecture of Erdős, Faber, and Lovász about $n$-colorings*.
  Canad. J. Math. (1981).
* [Ka92] Kahn, J., *Coloring nearly-disjoint hypergraphs with $n + o(n)$ colors*.
  J. Combin. Theory Ser. A (1992).
* [RoAl14] Romero, D. and Alonso-Pecina, F., *The Erdős–Faber–Lovász conjecture is true for
  $n \le 12$*. Discrete Math. Algorithms Appl. 6 (2014), 1450039.
* [KKKMO21] Kang, D. Y., Kelly, T., Kühn, D., Methuku, A. and Osthus, D., *A proof of the
  Erdős–Faber–Lovász conjecture*. Ann. of Math. (2023).
  [arXiv:2101.04698](https://arxiv.org/abs/2101.04698)
* [Pa26] Parobek, Lucas, *Three-Tier Pair-Budget Discharging Closure, Pairwise Balanced Reduction,
  and GPU Bitmask Certification for Erdős Problem #19 (The Erdős–Faber–Lovász Conjecture)*. (2026),
  [Manuscript PDF](https://github.com/doublegate/Erdos_19/blob/main/paper/Parobek_2026-10-27_Erdos19_Three_Tier_Discharging_Closure_EFL_Conjecture.pdf),
  [github.com/doublegate/Erdos_19](https://github.com/doublegate/Erdos_19).
-/

@[expose] public section

open Filter

namespace Erdos19

open scoped Classical in
/-- A configuration of `n` pairwise edge-disjoint copies of $K_n$ covering the vertex type `V`. -/
structure EFLConfig (V : Type*) (n : ℕ) where
  /-- The vertex sets of the `n` cliques. -/
  A : Fin n → Finset V
  /-- Each clique has exactly `n` vertices. -/
  card_eq : ∀ i, (A i).card = n
  /-- Two different cliques share at most one vertex, i.e. they are edge-disjoint. -/
  inter_le : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1
  /-- Every vertex lies in one of the cliques. -/
  cover : ∀ v, ∃ i, v ∈ A i

namespace EFLConfig

variable {V : Type*} {n : ℕ} (C : EFLConfig V n)

/-- The union graph: distinct vertices are adjacent iff they lie in a common clique. -/
def graph : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ i, u ∈ C.A i ∧ v ∈ C.A i
  symm := ⟨fun _ _ ⟨h, i, hu, hv⟩ => ⟨h.symm, i, hv, hu⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A vertex is *shared* if it lies in two different cliques. -/
def IsShared (v : V) : Prop := ∃ i j, i ≠ j ∧ v ∈ C.A i ∧ v ∈ C.A j

open scoped Classical in
/-- The finite set of shared vertices. -/
noncomputable def sharedSet : Finset V :=
  ((Finset.univ : Finset (Fin n)).biUnion C.A).filter C.IsShared

/-- The graph $G$ contains a copy of $K_n$, so $n \le \chi(G)$. -/
@[category textbook, AMS 5]
theorem le_chromaticNumber : (n : ℕ∞) ≤ C.graph.chromaticNumber := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hcl : C.graph.IsClique (C.A ⟨0, hn⟩ : Set V) := by
    intro u hu v hv huv
    exact ⟨huv, ⟨0, hn⟩, hu, hv⟩
  have := hcl.card_le_chromaticNumber
  rwa [C.card_eq] at this

/-- A vertex that is not shared lies in exactly one clique. -/
@[category API, AMS 5]
lemma eq_of_not_shared {v : V} (hv : ¬ C.IsShared v) {i j : Fin n}
    (hi : v ∈ C.A i) (hj : v ∈ C.A j) : i = j := by
  by_contra h
  exact hv ⟨i, j, h, hi, hj⟩

open scoped Classical in
/-- If the shared vertices can be coloured with $n$ colours so that shared vertices in a common
clique get distinct colours, then $G$ is $n$-colourable. -/
@[category textbook, AMS 5]
theorem colorable_of_sharedColoring (c : V → Fin n)
    (hc : ∀ i u v, u ∈ C.A i → v ∈ C.A i → C.IsShared u → C.IsShared v → c u = c v → u = v) :
    C.graph.Colorable n := by
  -- private vertices and free colours of each clique
  let P : Fin n → Finset V := fun i => (C.A i).filter (fun v => ¬ C.IsShared v)
  let U : Fin n → Finset V := fun i => (C.A i).filter C.IsShared
  let F : Fin n → Finset (Fin n) := fun i => Finset.univ \ (U i).image c
  have hcard : ∀ i, (P i).card ≤ (F i).card := by
    intro i
    have h1 : (U i).card + (P i).card = n := by
      rw [← C.card_eq i]; exact Finset.card_filter_add_card_filter_not _
    have h2 : ((U i).image c).card ≤ (U i).card := Finset.card_image_le
    have h3 : (F i).card = n - ((U i).image c).card := by
      simp [F, Finset.card_sdiff]
    omega
  have hne : ∀ i, Nonempty (P i ↪ F i) := fun i =>
    Function.Embedding.nonempty_of_card_le (by simpa using hcard i)
  let e : ∀ i, P i ↪ F i := fun i => Classical.choice (hne i)
  let idx : V → Fin n := fun v => Classical.choose (C.cover v)
  have hidx : ∀ v, v ∈ C.A (idx v) := fun v => Classical.choose_spec (C.cover v)
  let col : V → Fin n := fun v =>
    if h : C.IsShared v then c v
    else ((e (idx v) ⟨v, Finset.mem_filter.2 ⟨hidx v, h⟩⟩ : F (idx v)) : Fin n)
  have col_priv : ∀ v (hv : ¬ C.IsShared v) j (hj : v ∈ C.A j),
      col v = ((e j ⟨v, Finset.mem_filter.2 ⟨hj, hv⟩⟩ : F j) : Fin n) := by
    intro v hv j hj
    have key : ∀ i (hi : i = j) (p : v ∈ P i), ((e i ⟨v, p⟩ : F i) : Fin n) =
        ((e j ⟨v, Finset.mem_filter.2 ⟨hj, hv⟩⟩ : F j) : Fin n) := by
      rintro i rfl p; rfl
    simp only [col, dif_neg hv]
    exact key _ (C.eq_of_not_shared hv (hidx v) hj) _
  have col_free : ∀ v (hv : ¬ C.IsShared v) j (hj : v ∈ C.A j), col v ∈ F j := by
    intro v hv j hj
    rw [col_priv v hv j hj]; exact Subtype.property _
  refine ⟨SimpleGraph.Coloring.mk col ?_⟩
  rintro u v ⟨huv, j, hu, hv⟩ heq
  by_cases su : C.IsShared u <;> by_cases sv : C.IsShared v
  · have : col u = c u := dif_pos su
    have : col v = c v := dif_pos sv
    exact huv (hc j u v hu hv su sv (by simp_all))
  · have h1 := col_free v sv j hv
    have : col u = c u := dif_pos su
    simp only [F, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image] at h1
    exact h1 ⟨u, Finset.mem_filter.2 ⟨hu, su⟩, by rw [← this, heq]⟩
  · have h1 := col_free u su j hu
    have : col v = c v := dif_pos sv
    simp only [F, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image] at h1
    exact h1 ⟨v, Finset.mem_filter.2 ⟨hv, sv⟩, by rw [← this, ← heq]⟩
  · rw [col_priv u su j hu, col_priv v sv j hv] at heq
    have := (e j).injective (Subtype.ext heq)
    exact huv (congrArg Subtype.val this)

open scoped Classical in
/-- There are at most $\binom{n}{2}$ shared vertices, since two cliques share at most one
vertex. -/
@[category textbook, AMS 5]
theorem card_sharedSet_le : C.sharedSet.card ≤ n.choose 2 := by
  -- assign to each shared vertex a pair of cliques containing it
  let f : V → Finset (Fin n) := fun v =>
    if h : C.IsShared v then {Classical.choose h, Classical.choose (Classical.choose_spec h)}
    else ∅
  have hf : ∀ v ∈ C.sharedSet, f v ∈ (Finset.univ : Finset (Fin n)).powersetCard 2 ∧
      ∀ x ∈ f v, v ∈ C.A x := by
    intro v hv
    have hs : C.IsShared v := (Finset.mem_filter.1 hv).2
    obtain ⟨hij, hi, hj⟩ := Classical.choose_spec (Classical.choose_spec hs)
    simp only [f, dif_pos hs]
    refine ⟨Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, Finset.card_pair hij⟩, ?_⟩
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hi
    · rw [Finset.mem_singleton.1 hx]; exact hj
  have hinj : Set.InjOn f C.sharedSet := by
    intro u hu v hv huv
    obtain ⟨hpu, hu'⟩ := hf u hu
    obtain ⟨hpv, hv'⟩ := hf v hv
    obtain ⟨a, b, hab, hfab⟩ := Finset.card_eq_two.1 (Finset.mem_powersetCard.1 hpu).2
    have ha : a ∈ f u := by rw [hfab]; simp
    have hb : b ∈ f u := by rw [hfab]; simp
    have hle := C.inter_le a b hab
    have hu2 : u ∈ C.A a ∩ C.A b := Finset.mem_inter.2 ⟨hu' a ha, hu' b hb⟩
    have hv2 : v ∈ C.A a ∩ C.A b :=
      Finset.mem_inter.2 ⟨hv' a (huv ▸ ha), hv' b (huv ▸ hb)⟩
    exact Finset.card_le_one.1 hle u hu2 v hv2
  have := Finset.card_le_card_of_injOn f (t := (Finset.univ : Finset (Fin n)).powersetCard 2)
    (fun v hv => (hf v hv).1) hinj
  simpa [Finset.card_powersetCard] using this

end EFLConfig

open EFLConfig

/--
If $G$ is an edge-disjoint union of $n$ copies of $K_n$, then is $\chi(G) = n$?

Resolved in the affirmative for all sufficiently large $n$ by Kang, Kelly, Kühn, Methuku, and
Osthus [KKKMO21]; see [Pa26] for Pairwise Balanced Design (PBD) completion, Vizing–Fournier
shadow-slack and Fournier 2-core discharging (unconditional for $\chi'(\mathcal{E}_{\ge 3}) \le 2$
and $\mathrm{AG}(2,q)^{+p}$ across all prime powers $q$), and exhaustive GPU bitmask certification
across $3 \le n \le 25$.
-/
@[category research open, question, AMS 5]
theorem erdos_19 :
    ∀ (V : Type) (n : ℕ) (C : EFLConfig V n), C.graph.chromaticNumber = n := by
  sorry

open scoped Classical in
/--
The Erdős–Faber–Lovász conjecture holds for $n \le 3$.
-/
@[category test, AMS 5]
theorem erdos_19.variants.le_three {V : Type*} {n : ℕ} (C : EFLConfig V n) (hn : n ≤ 3) :
    C.graph.chromaticNumber = n := by
  refine le_antisymm ?_ C.le_chromaticNumber
  apply SimpleGraph.Colorable.chromaticNumber_le
  have hS : C.sharedSet.card ≤ n := by
    have h1 := C.card_sharedSet_le
    have h2 : n.choose 2 ≤ n := by interval_cases n <;> decide
    omega
  -- colour the shared vertices injectively
  let c : V → Fin n := fun v =>
    if h : v ∈ C.sharedSet then Fin.castLE hS (C.sharedSet.equivFin ⟨v, h⟩)
    else ⟨0, by
      obtain ⟨i, hi⟩ := C.cover v
      rw [← C.card_eq i]; exact Finset.card_pos.2 ⟨v, hi⟩⟩
  refine C.colorable_of_sharedColoring c ?_
  intro i u v hu hv su sv huv
  have mu : u ∈ C.sharedSet := Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨i, by simp, hu⟩, su⟩
  have mv : v ∈ C.sharedSet := Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨i, by simp, hv⟩, sv⟩
  simp only [c, dif_pos mu, dif_pos mv] at huv
  have := C.sharedSet.equivFin.injective (Fin.castLE_injective hS huv)
  exact congrArg Subtype.val this

/--
Hindman [Hi81] proved the Erdős–Faber–Lovász conjecture for $n < 10$.
-/
@[category research solved, AMS 5]
theorem erdos_19.variants.lt_ten :
    ∀ (V : Type) (n : ℕ) (C : EFLConfig V n), n < 10 → C.graph.chromaticNumber = n := by
  sorry

/--
An affirmative answer to `erdos_19` immediately implies `erdos_19.variants.lt_ten`.
-/
@[category API, AMS 5]
theorem erdos_19.variants.erdos_19_implies_lt_ten
    (h : ∀ (V : Type) (n : ℕ) (C : EFLConfig V n), C.graph.chromaticNumber = n) :
    ∀ (V : Type) (n : ℕ) (C : EFLConfig V n), n < 10 → C.graph.chromaticNumber = n := by
  intro V n C _
  exact h V n C

/--
Romero and Alonso-Pecina [RoAl14] proved the Erdős–Faber–Lovász conjecture for $n \le 12$.
-/
@[category research solved, AMS 5]
theorem erdos_19.variants.le_twelve :
    ∀ (V : Type) (n : ℕ) (C : EFLConfig V n), n ≤ 12 → C.graph.chromaticNumber = n := by
  sorry

/--
An affirmative answer to `erdos_19` immediately implies `erdos_19.variants.le_twelve`.
-/
@[category API, AMS 5]
theorem erdos_19.variants.erdos_19_implies_le_twelve
    (h : ∀ (V : Type) (n : ℕ) (C : EFLConfig V n), C.graph.chromaticNumber = n) :
    ∀ (V : Type) (n : ℕ) (C : EFLConfig V n), n ≤ 12 → C.graph.chromaticNumber = n := by
  intro V n C _
  exact h V n C

/--
Kahn [Ka92] proved that $\chi(G) \le (1 + o(1))n$.
-/
@[category research solved, AMS 5]
theorem erdos_19.variants.kahn :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ (V : Type) (C : EFLConfig V n),
      C.graph.Colorable ⌊(1 + ε) * n⌋₊ := by
  sorry

/--
Kang, Kelly, Kühn, Methuku and Osthus [KKKMO21] proved the Erdős–Faber–Lovász conjecture for
all sufficiently large $n$.
-/
@[category research solved, AMS 5]
theorem erdos_19.variants.large_n :
    ∀ᶠ n in atTop, ∀ (V : Type) (C : EFLConfig V n), C.graph.chromaticNumber = n := by
  sorry

/--
An affirmative answer to `erdos_19` immediately implies `erdos_19.variants.large_n`.
-/
@[category API, AMS 5]
theorem erdos_19.variants.erdos_19_implies_large_n
    (h : ∀ (V : Type) (n : ℕ) (C : EFLConfig V n), C.graph.chromaticNumber = n) :
    ∀ᶠ n in atTop, ∀ (V : Type) (C : EFLConfig V n), C.graph.chromaticNumber = n := by
  exact Filter.Eventually.of_forall (fun n V C => h V n C)

/-! ## Arithmetic Lemmas & Certified Projective Plane Witnesses Used in [Pa26] -/

/--
**Arithmetic Lemma for Theorem 2.1(i) of [Pa26] (Additive Partition Conservation):**
For natural numbers `total_pairs`, `p_blocks`, and `e2` satisfying `p_blocks + e2 = total_pairs`,
`total_pairs - p_blocks = e2` and `p_blocks ≤ total_pairs` (used for the PBD 2-edge pair partition
`p_blocks + e2 = n * (n - 1) / 2` in Theorem 2.1(i) of [Pa26]).
-/
@[category API, AMS 5,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_19/blob/main/Erdos19/Proofs.lean#L36"]
theorem erdos_19.variants.pbd_two_edge_completion_conservation (total_pairs p_blocks e2 : ℕ)
    (h_partition : p_blocks + e2 = total_pairs) :
    total_pairs - p_blocks = e2 ∧ p_blocks ≤ total_pairs := by
  sorry

/--
**Arithmetic Lemma for Theorem 3.2(ii) [2.2(b)] of [Pa26] (Single-Triple Capacity Inequality):**
For any natural number `t ≥ 3`, if `m = 2 * t * t + t - 2` and `cap_nm1 = t + (2 * t - 1) * t`,
then `cap_nm1 = 2 * t * t < m`. In Theorem 3.2(ii) of [Pa26], `m` is the edge count of the
single-triple PBD `H_1(2t + 1)` and `cap_nm1` is the maximum hyperedge capacity of `2t = n - 1`
color classes when one class contains the 3-block (`t` edges) and `2t - 1` classes contain at
most `t` 2-edges each.
-/
@[category API, AMS 5,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_19/blob/main/Erdos19/Proofs.lean#L51"]
theorem erdos_19.variants.single_triple_parity_saturation_chromatic (t m cap_nm1 : ℕ)
    (ht : 3 ≤ t)
    (hm : m = 2 * t * t + t - 2)
    (hcap : cap_nm1 = t + (2 * t - 1) * t) :
    cap_nm1 < m := by
  sorry

/--
**Arithmetic Lemma for Theorem 3.3(i)–(ii) [2.3(a)–(b)] of [Pa26] (Two-Triple Capacity Inequality at `t = 3`):**
For `t = 3`, `m = 2 * t * t + t - 4 = 17`, and `cap_disj = 2 * t + (2 * t - 2) * (t - 1) = 14`,
`cap_disj < m` holds on `ℕ`. In Theorem 3.3 of [Pa26], this compares the 6-color capacity bound
against the 17 hyperedges of the disjoint two-triple PBD `H_{2,disj}(7)`.
-/
@[category API, AMS 5,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_19/blob/main/Erdos19/Proofs.lean#L71"]
theorem erdos_19.variants.two_triple_disjoint_volume_starvation (t m cap_disj : ℕ)
    (ht : t = 3)
    (hm : m = 2 * t * t + t - 4)
    (hcap : cap_disj = 2 * t + (2 * t - 2) * (t - 1)) :
    cap_disj < m := by
  sorry

/--
**Arithmetic Lemma for Theorem 3.4(i) [2.4(a)] of [Pa26] (Linear Elimination for Shadow-Slack):**
For natural numbers satisfying `n_minus_1 = d_2 + 2 * d_ge3 + rank_excess` and
`delta_vf + q_prime = 2 * d_ge3 + match_v + rank_excess + 1`, eliminating `2 * d_ge3 + rank_excess`
yields `n_minus_1 + match_v + 1 = d_2 + delta_vf + q_prime` (the arithmetic elimination step in
the Vizing–Fournier shadow-slack identity of Theorem 3.4(i) in [Pa26]).
-/
@[category API, AMS 5,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_19/blob/main/Erdos19/Proofs.lean#L88"]
theorem erdos_19.variants.vizing_fournier_shadow_slack_identity
    (n_minus_1 d_2 d_ge3 rank_excess match_v q_prime delta_vf : ℕ)
    (h_pbd_deg : n_minus_1 = d_2 + 2 * d_ge3 + rank_excess)
    (h_delta : delta_vf + q_prime = 2 * d_ge3 + match_v + rank_excess + 1) :
    n_minus_1 + match_v + 1 = d_2 + delta_vf + q_prime := by
  sorry

/--
**Arithmetic Lemma for Theorem 3.5(i) & 3.11(i) of [Pa26] (Forest Edge-Double Identity):**
For natural numbers `1 ≤ c ≤ V_T` and `E_T = V_T - c`, `2 * E_T + 2 * c = 2 * V_T` and
`2 * E_T < 2 * V_T` (the arithmetic step relating forest edge count `E_T = V_T - c` to twice
the vertex count `2 * V_T` in Theorem 3.5(i) of [Pa26]).
-/
@[category API, AMS 5,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_19/blob/main/Erdos19/Proofs.lean#L103"]
theorem erdos_19.variants.fournier_forest_degree_sum_lt (V_T E_T c : ℕ)
    (_hV : 1 ≤ V_T) (hc : 1 ≤ c) (hc_le : c ≤ V_T) (h_forest : E_T = V_T - c) :
    2 * E_T + 2 * c = 2 * V_T ∧ 2 * E_T < 2 * V_T := by
  sorry

/--
**Arithmetic Lemma for Theorem 3.6(i) [2.6(a)] of [Pa26] (Additive Cancellation Identity):**
For natural numbers `S_B`, `pair_twice`, and `e2_I` with `2 * e2_I ≤ pair_twice`,
`(S_B + 2 * e2_I) + (pair_twice - 2 * e2_I) = S_B + pair_twice` (the arithmetic cancellation step
in the Shadow-Slack identity of Theorem 3.6(i) in [Pa26]).
-/
@[category API, AMS 5,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_19/blob/main/Erdos19/Proofs.lean#L116"]
theorem erdos_19.variants.shadow_slack_identity (S_B pair_twice e2_I : ℕ)
    (h_le : 2 * e2_I ≤ pair_twice) :
    (S_B + 2 * e2_I) + (pair_twice - 2 * e2_I) = S_B + pair_twice := by
  sorry

/--
**Arithmetic Lemma for Theorem 3.7(a) [2.6(b)] of [Pa26] (Linear Degree-Sum Inequality):**
For natural numbers `t ≥ 1` and `delta ≥ 1` with `delta + 1 ≤ 2 * t`, any `deg_sum_U` satisfying
`deg_sum_U ≤ 2 * delta + (2 * t - 1) * (delta - 1)` also satisfies `deg_sum_U ≤ 2 * t * delta`
(the arithmetic inequality used in the odd-set degree-sum bound of Theorem 3.7(a) in [Pa26]).
-/
@[category API, AMS 5,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_19/blob/main/Erdos19/Proofs.lean#L129"]
theorem erdos_19.variants.edmonds_blossom_odd_set_slack_bound
    (t delta deg_sum_U : ℕ)
    (ht : 1 ≤ t) (hdelta : 1 ≤ delta)
    (h_large_odd : delta + 1 ≤ 2 * t)
    (h_deg_bound : deg_sum_U ≤ 2 * delta + (2 * t - 1) * (delta - 1)) :
    deg_sum_U ≤ 2 * t * delta := by
  sorry

/--
**Arithmetic Lemma for Theorem 3.8(i) [2.8(a)] of [Pa26] (Linear Slack Increment Identity):**
For natural numbers `1 ≤ p ≤ d_ge3` and `2 * d_ge3 ≤ n`, `(n - p) - 2 * (d_ge3 - p) = (n - 2 * d_ge3) + p`
and `n - 2 * d_ge3 < (n - p) - 2 * (d_ge3 - p)` (the arithmetic step showing a `+p` slack increase
when `d_ge3` decreases by `p` and `n` decreases by `p` in Theorem 3.8(i) of [Pa26]).
-/
@[category API, AMS 5,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_19/blob/main/Erdos19/Proofs.lean#L155"]
theorem erdos_19.variants.parallel_class_peeling_slack (n d_ge3 p : ℕ)
    (hp : 1 ≤ p) (hd : p ≤ d_ge3) (hn : 2 * d_ge3 ≤ n) :
    (n - p) - 2 * (d_ge3 - p) = (n - 2 * d_ge3) + p ∧
      n - 2 * d_ge3 < (n - p) - 2 * (d_ge3 - p) := by
  sorry

/--
**Arithmetic Lemma for Theorem 3.9(i) [2.9(a)] of [Pa26] (Square Overflow Inequality):**
For natural numbers `n, s` with `n ≤ s * (s + 2)`, `n < (s + 1) * (s + 1)` since
`(s + 1)^2 = s(s + 2) + 1` (the arithmetic step used in Theorem 3.9(i) of [Pa26] to show that
`s + 1` disjoint blocks of size `≥ s + 1` require more than `s(s + 2) ≥ n` vertices).
-/
@[category API, AMS 5,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_19/blob/main/Erdos19/Proofs.lean#L169"]
theorem erdos_19.variants.large_block_disjoint_overflow (n s : ℕ)
    (hn : n ≤ s * (s + 2)) :
    n < (s + 1) * (s + 1) := by
  sorry

/--
**Arithmetic Lemma for Theorem 3.10(i) [2.9(b)] of [Pa26] (Polynomial Slack Identity for `1 ≤ p ≤ q`):**
Whenever `1 ≤ p ≤ q` and `q ≥ 2`, `(q - 1) * p + (q + 1) + (q - 1) * (q - p) + (p - 1) = q * q + p`
(the arithmetic identity comparing `(q - 1)p + (q + 1)` and `q^2 + p` in Theorem 3.10(i) of [Pa26]).
-/
@[category API, AMS 5,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_19/blob/main/Erdos19/Proofs.lean#L187"]
theorem erdos_19.variants.ag2q_ideal_point_exact_slack_formula (q p : ℕ)
    (hq : 2 ≤ q) (hp_pos : 1 ≤ p) (hp : p ≤ q) :
    (q - 1) * p + (q + 1) + (q - 1) * (q - p) + (p - 1) = q * q + p := by
  sorry

/--
**Arithmetic Lemma for Theorem 3.10(i) & 3.11(ii) of [Pa26] (Polynomial Inequality `(q - 1)p + (q + 1) ≤ q^2 + p`):**
For every natural number `q ≥ 2` and `0 ≤ p ≤ q`, `(q - 1) * p + (q + 1) ≤ q * q + p`
(the arithmetic inequality showing that the formula `(q - 1)p + (q + 1)` does not exceed `q^2 + p`
in Theorem 3.10(i) of [Pa26]).
-/
@[category API, AMS 5,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_19/blob/main/Erdos19/Proofs.lean#L205"]
theorem erdos_19.variants.ag2q_ideal_point_chromatic_le_n (q p : ℕ)
    (hq : 2 ≤ q) (hp : p ≤ q) :
    (q - 1) * p + (q + 1) ≤ q * q + p := by
  sorry

/--
**Arithmetic Lemma for Theorem 3.10(ii) & 3.11(i) of [Pa26] (Three-Term Partition Subtraction):**
For natural numbers `total_pairs`, `large_pairs`, `med_pairs`, and `e2` satisfying
`large_pairs + med_pairs + e2 = total_pairs`, `total_pairs - large_pairs - med_pairs = e2`.
-/
@[category API, AMS 5,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_19/blob/main/Erdos19/Proofs.lean#L230"]
theorem erdos_19.variants.three_tier_pair_budget_nonneg (total_pairs large_pairs med_pairs e2 : ℕ)
    (h_pbd : large_pairs + med_pairs + e2 = total_pairs) :
    total_pairs - large_pairs - med_pairs = e2 := by
  sorry

/--
**Arithmetic Lemma for Theorem 3.11(a) [2.10(a)] of [Pa26] (Global Linear Conservation Identity):**
For natural numbers `1 ≤ q' ≤ n` and `F_tot ≤ e2` satisfying `2 * (P_L + P_M + e2) = n * (n - 1)`
and `sum_delta_vf + n * (q' - 1) = 2 * (P_L + P_M + F_tot)`, we have
`sum_delta_vf + 2 * (e2 - F_tot) = n * (n - q')` and `2 * (P_L + P_M + F_tot) = n * (q' - 1) + sum_delta_vf`
(the linear elimination step in Theorem 3.11(a) of [Pa26]).
-/
@[category API, AMS 5,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_19/blob/main/Erdos19/Proofs.lean#L242"]
theorem erdos_19.variants.global_shadow_slack_conservation
    (n q' P_L P_M e2 F_tot sum_delta_vf : ℕ)
    (hq_pos : 1 ≤ q') (hq_le : q' ≤ n) (hF_le : F_tot ≤ e2)
    (h_pbd_twice : 2 * (P_L + P_M + e2) = n * (n - 1))
    (h_slack_sum : sum_delta_vf + n * (q' - 1) = 2 * (P_L + P_M + F_tot)) :
    sum_delta_vf + 2 * (e2 - F_tot) = n * (n - q') ∧
    2 * (P_L + P_M + F_tot) = n * (q' - 1) + sum_delta_vf := by
  sorry

/--
**Arithmetic Lemma for Theorem 3.11(c) [2.10(c)] of [Pa26] (Linear Budget Contradiction):**
For natural numbers satisfying `F_tot ≤ e2`, `2 * (P_L + P_M + e2) = n * (n - 1)`, and
`2 * (e2 - F_tot) = k * (n - q') + deg_sum_outside`, the strict inequality
`n * (n - 1) < 2 * (P_L + P_M + F_tot) + k * (n - q') + deg_sum_outside` is impossible (`False`).
-/
@[category API, AMS 5,
  formal_proof using lean4 at "https://github.com/doublegate/Erdos_19/blob/main/Erdos19/Proofs.lean#L261"]
theorem erdos_19.variants.three_tier_fournier_obstruction_bound
    (n q' k P_L P_M e2 F_tot deg_sum_outside : ℕ)
    (_hk : 3 ≤ k) (_hk_le : k ≤ n) (_hq_le : q' ≤ n) (hF_le : F_tot ≤ e2)
    (h_pbd_twice : 2 * (P_L + P_M + e2) = n * (n - 1))
    (h_core_deg : 2 * (e2 - F_tot) = k * (n - q') + deg_sum_outside)
    (h_budget_exceeds : n * (n - 1) < 2 * (P_L + P_M + F_tot) + k * (n - q') + deg_sum_outside) :
    False := by
  sorry

/-- Unordered pairs covered by a block of vertices. -/
def pairsOfBlock : List ℕ → List (ℕ × ℕ)
  | [] => []
  | u :: rest => (rest.map (fun v => if u < v then (u, v) else (v, u))) ++ pairsOfBlock rest

/-- Concatenation of all vertex pairs covered across a family of blocks. -/
def allBlockPairs (blocks : List (List ℕ)) : List (ℕ × ℕ) :=
  blocks.foldr (fun b acc => pairsOfBlock b ++ acc) []

/-- Boolean check that a list of natural numbers contains no duplicate entries. -/
def listNoDups : List ℕ → Bool
  | [] => true
  | v :: rest => !(rest.contains v) && listNoDups rest

/-- Boolean check that a list of vertex pairs contains no duplicate entries. -/
def pairListNoDups : List (ℕ × ℕ) → Bool
  | [] => true
  | p :: rest => !(rest.contains p) && pairListNoDups rest

/-- Boolean verifier that `blocks` forms a `(n, k, 1)` projective plane on `{0, ..., n-1}`. -/
def isCertifiedProjectivePlane (n k : ℕ) (blocks : List (List ℕ)) : Bool :=
  (blocks.length == n) &&
  (blocks.all (fun b => b.length == k && listNoDups b && b.all (fun v => v < n))) &&
  (let pairs := allBlockPairs blocks
   (pairs.length == n * (n - 1) / 2) && pairListNoDups pairs)

/-- Fano plane $\mathrm{PG}(2, 2)$ on $n = 7$ vertices with $7$ lines of size $k = 3$. -/
def fanoPlanePG22 : List (List ℕ) :=
  [[0, 1, 3], [1, 2, 4], [2, 3, 5], [3, 4, 6], [4, 5, 0], [5, 6, 1], [6, 0, 2]]

/--
Machine-checked verification that the Fano plane $\mathrm{PG}(2, 2)$ on $n = 7$ vertices
([Pa26, Table 1]) covers all $\binom{7}{2} = 21$ vertex pairs without duplicates.
-/
@[category test, AMS 5]
theorem fanoPlanePG22_certified :
    isCertifiedProjectivePlane 7 3 fanoPlanePG22 = true := by
  decide

/-- Projective plane $\mathrm{PG}(2, 3)$ on $n = 13$ vertices with $13$ lines of size $k = 4$. -/
def projectivePlanePG23 : List (List ℕ) :=
  [[0, 1, 3, 9], [1, 2, 4, 10], [2, 3, 5, 11], [3, 4, 6, 12],
   [4, 5, 7, 0], [5, 6, 8, 1],  [6, 7, 9, 2],  [7, 8, 10, 3],
   [8, 9, 11, 4], [9, 10, 12, 5], [10, 11, 0, 6], [11, 12, 1, 7],
   [12, 0, 2, 8]]

/--
Machine-checked verification that the projective plane $\mathrm{PG}(2, 3)$ on $n = 13$ vertices
([Pa26, Table 1]) covers all $\binom{13}{2} = 78$ vertex pairs without duplicates.
-/
@[category test, AMS 5]
theorem projectivePlanePG23_certified :
    isCertifiedProjectivePlane 13 4 projectivePlanePG23 = true := by
  decide

end Erdos19
