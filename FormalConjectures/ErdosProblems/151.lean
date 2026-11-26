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
# Erdős Problem 151

*References:*
- [erdosproblems.com/151](https://www.erdosproblems.com/151)
- [Er88] Erdős, P., *Problems and results in combinatorial analysis and graph theory*.
  Discrete Math. (1988), 81-92.
- [EGT92] Erdős, P. and Gallai, T. and Tuza, Zs., *Covering the cliques of a graph with
  vertices*. Discrete Math. (1992), 279-289.
-/

@[expose] public section

namespace Erdos151

open SimpleGraph

/-- $H(n)$: the largest `k` such that every triangle-free graph on `n` vertices contains an
independent set on `k` vertices. -/
noncomputable def H (n : ℕ) : ℕ :=
  sSup {k | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → ∃ s, G.IsNIndepSet k s}

/--
For a graph $G$, let $\tau(G)$ denote the minimal number of vertices that include at least one
from each maximal clique of $G$ on at least two vertices. Let $H(n)$ be maximal such that every
triangle-free graph on $n$ vertices contains an independent set on $H(n)$ vertices.

If $G$ is a graph on $n$ vertices, is $\tau(G)\leq n-H(n)$?

Erdős remarked that this is perhaps completely wrongheaded [Er88].
-/
@[category research open, question, AMS 5]
theorem erdos_151 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), cliqueTransversalNumber G ≤ n - H n := by
  sorry

/--
Erdős and Gallai made no progress on the question even when $G$ is $K_4$-free [Er88].
-/
@[category research open, question, AMS 5]
theorem erdos_151.variants.cliqueFree_four :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 4 →
      cliqueTransversalNumber G ≤ n - H n := by
  sorry

/-- If no big maximal clique lies inside `U`, then the complement of `U` is a clique
transversal, so $\tau(G)\leq n-|U|$. -/
lemma cliqueTransversalNumber_le_of_not_subset {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Finset (Fin n)) (hU : ∀ c, G.IsBigMaximalClique c → ¬ c ⊆ U) :
    cliqueTransversalNumber G ≤ n - U.card := by
  classical
  refine Nat.sInf_le ⟨Uᶜ, ?_, ?_⟩
  · intro c hc
    obtain ⟨v, hv, hvU⟩ := Finset.not_subset.mp (hU c hc)
    exact ⟨v, hv, Finset.mem_compl.mpr hvU⟩
  · simp [Finset.card_compl]

/-- No big maximal clique lies inside an independent set. -/
lemma not_subset_of_isIndepSet {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n))
    (hU : G.IsIndepSet (U : Set (Fin n))) (c : Finset (Fin n)) (hc : G.IsBigMaximalClique c) :
    ¬ c ⊆ U := by
  intro hcU
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc.2
  exact hU (hcU ha) (hcU hb) hab (hc.1.1 ha hb hab)

/--
If $G$ is triangle-free, then $\tau(G)\leq n-H(n)$: the complement of an independent set meets
every edge.
-/
@[category research solved, AMS 5]
theorem erdos_151.variants.cliqueFree_three (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 3) : cliqueTransversalNumber G ≤ n - H n := by
  have hmem : H n ∈ {k | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → ∃ s, G.IsNIndepSet k s} := by
    refine Nat.sSup_mem ⟨0, fun G _ ↦ ⟨∅, by simp [isNIndepSet_iff]⟩⟩ ⟨n, fun k hk ↦ ?_⟩
    obtain ⟨s, hs⟩ := hk ⊥ (by simp [CliqueFree, isNClique_iff]; intro t ht h3; obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < t.card); exact hab (ht ha hb))
    rw [← hs.card_eq]
    simpa using s.card_le_univ
  obtain ⟨s, hs⟩ := hmem G hG
  rw [← hs.card_eq]
  exact cliqueTransversalNumber_le_of_not_subset G s
    (not_subset_of_isIndepSet G s hs.isIndepSet)

/--
It is easy to see that $\tau(G)\leq n-\sqrt{n}$. We state this with $\lfloor\sqrt{n}\rfloor$:
with the real square root the bound fails for a single edge ($n = 2$, $\tau = 1$).
-/
@[category research solved, AMS 5]
theorem erdos_151.variants.sqrt_bound (n : ℕ) (G : SimpleGraph (Fin n)) :
    cliqueTransversalNumber G ≤ n - Nat.sqrt n := by
  classical
  suffices h : ∃ U : Finset (Fin n), Nat.sqrt n ≤ U.card ∧
      ∀ c, G.IsBigMaximalClique c → ¬ c ⊆ U by
    obtain ⟨U, hcard, hU⟩ := h
    exact (cliqueTransversalNumber_le_of_not_subset G U hU).trans (by omega)
  by_cases hdeg : ∃ v, Nat.sqrt n ≤ (G.neighborFinset v).card
  · -- a neighbourhood contains no maximal clique
    obtain ⟨v, hv⟩ := hdeg
    refine ⟨G.neighborFinset v, hv, fun c hc hcU ↦ ?_⟩
    have hclique : G.IsClique ((insert v c : Finset (Fin n)) : Set (Fin n)) := by
      rw [Finset.coe_insert]
      refine hc.1.1.insert fun b hb _ ↦ ?_
      simpa using hcU hb
    have hle := hc.1.2 hclique (Finset.subset_insert v c)
    have hvc : v ∈ c := hle (Finset.mem_insert_self v c)
    simpa using hcU hvc
  · -- all degrees are small: a maximum independent set is large
    push Not at hdeg
    obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image
      (Finset.univ.filter fun I : Finset (Fin n) ↦ G.IsIndepSet (I : Set (Fin n)))
      Finset.card ⟨∅, by simp⟩
    rw [Finset.mem_filter] at hI
    refine ⟨I, ?_, not_subset_of_isIndepSet G I hI.2⟩
    have hcover : (Finset.univ : Finset (Fin n)) ⊆ I ∪ I.biUnion (fun v ↦ G.neighborFinset v) := by
      intro w _
      by_contra hw
      rw [Finset.mem_union, not_or] at hw
      obtain ⟨hwI, hwN⟩ := hw
      have hind : G.IsIndepSet ((insert w I : Finset (Fin n)) : Set (Fin n)) := by
        rw [Finset.coe_insert, isIndepSet_iff]
        rw [isIndepSet_iff] at hI
        refine hI.2.insert fun b hb _ ↦ ⟨fun hadj ↦ hwN ?_, fun hadj ↦ hwN ?_⟩
        · exact Finset.mem_biUnion.mpr ⟨b, hb, by simpa using hadj.symm⟩
        · exact Finset.mem_biUnion.mpr ⟨b, hb, by simpa using hadj⟩
      have := hmax (insert w I) (by simpa using hind)
      rw [Finset.card_insert_of_notMem hwI] at this
      omega
    have h1 : n ≤ I.card + I.card * (Nat.sqrt n - 1) := by
      calc n = (Finset.univ : Finset (Fin n)).card := by simp
        _ ≤ (I ∪ I.biUnion (fun v ↦ G.neighborFinset v)).card := Finset.card_le_card hcover
        _ ≤ I.card + (I.biUnion (fun v ↦ G.neighborFinset v)).card := Finset.card_union_le _ _
        _ ≤ I.card + ∑ v ∈ I, (G.neighborFinset v).card :=
          Nat.add_le_add_left Finset.card_biUnion_le _
        _ ≤ I.card + I.card * (Nat.sqrt n - 1) := by
          refine Nat.add_le_add_left ?_ _
          have := Finset.sum_le_card_nsmul I (fun v ↦ (G.neighborFinset v).card)
            (Nat.sqrt n - 1) fun v _ ↦ by have := hdeg v; omega
          rwa [smul_eq_mul] at this
    by_contra hlt
    push Not at hlt
    have h2 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
    have h3 : I.card + I.card * (Nat.sqrt n - 1) = I.card * Nat.sqrt n := by
      obtain ⟨m, hm⟩ : ∃ m, Nat.sqrt n = m + 1 := ⟨Nat.sqrt n - 1, by omega⟩
      rw [hm]; simp; ring
    have h4 : (I.card + 1) * Nat.sqrt n ≤ Nat.sqrt n * Nat.sqrt n :=
      Nat.mul_le_mul_right _ hlt
    nlinarith

end Erdos151
