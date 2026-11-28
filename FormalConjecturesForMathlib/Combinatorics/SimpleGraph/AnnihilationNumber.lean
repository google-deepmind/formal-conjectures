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

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Multiset.Interval
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Degrees

@[expose] public section

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The annihilation number of a graph. This is the largest number of degrees that can be added
together without going over the total number of edges of that graph. -/
def annihilationNumber (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  -- Calculate the limit: The number of edges (Sum of degrees / 2)
  letI limit := G.edgeFinset.card

  -- The set of all multisets of degrees that sum to less than or equal to `limit`
  Finset.Iic (degreeMultiset G)
    |>.filter (fun S ↦ Multiset.sum S ≤ limit)
    |>.sup Multiset.card

/--
Computes the annihilation number of a graph G.

It calculates the degree sequence, sorts it ascendingly, and finds the largest prefix length 'k'
(where `0 ≤ k ≤ |V(G)|`) such that the sum of the prefix is less than or equal to the sum of the corresponding suffix.
-/
noncomputable def annihilationNumber' (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  -- 1. Get the degree sequence sorted in ascending order.
  -- G.degree_list returns the list of degrees.
  letI degrees := (Finset.univ.val.map fun v => G.degree v).sort (· ≤ ·)

  -- 2. Define the condition for the annihilation number.
  -- k represents the number of smallest degrees considered (the length of the prefix).
  letI condition (k : ℕ) : Bool := (degrees.take k).sum ≤ (degrees.drop k).sum

  -- 3. Find the maximum k in {0, ..., n} satisfying the condition.
  -- List.range (n + 1) generates the list [0, 1, ..., n].
  letI candidates := (List.range (Fintype.card α + 1)).filter condition

  -- 4. Return the maximum candidate.
  -- The list of candidates is guaranteed to be non-empty because k=0 always satisfies
  -- the condition (0 ≤ sum of all degrees).
  candidates.getLast!

private lemma sum_take_le_sum_of_le :
    ∀ {L : List ℕ}, L.Pairwise (· ≤ ·) → ∀ {S : Multiset ℕ}, S ≤ (L : Multiset ℕ) →
      (L.take (Multiset.card S)).sum ≤ S.sum
  | [], _, S, hS => by
    have h0 : S = 0 := Multiset.le_zero.mp hS
    simp [h0]
  | a :: rest, hL, S, hS => by
    rw [List.pairwise_cons] at hL
    rcases hL with ⟨ha_le, hrest⟩
    by_cases hS0 : S = 0
    · simp [hS0]
    · by_cases haS : a ∈ S
      · have hS_eq : a ::ₘ (S.erase a) = S := Multiset.cons_erase haS
        have hS'_le : S.erase a ≤ (rest : Multiset ℕ) := by
          rw [← Multiset.cons_le_cons_iff a, hS_eq]
          exact hS
        have hcard : Multiset.card S = Multiset.card (S.erase a) + 1 := by
          simpa [Multiset.card_cons] using congrArg Multiset.card hS_eq.symm
        conv_lhs => rw [hcard, List.take_succ_cons, List.sum_cons]
        conv_rhs => rw [← hS_eq, Multiset.sum_cons]
        exact Nat.add_le_add_left (sum_take_le_sum_of_le hrest hS'_le) a
      · have hS_rest : S ≤ (rest : Multiset ℕ) := by
          rw [Multiset.le_iff_count] at hS ⊢
          intro x
          have hx := hS x
          by_cases hxa : x = a
          · subst hxa
            rw [Multiset.count_eq_zero.mpr haS]
            exact Nat.zero_le _
          · change S.count x ≤ (a ::ₘ (rest : Multiset ℕ)).count x at hx
            rw [Multiset.count_cons_of_ne hxa] at hx
            exact hx
        obtain ⟨b, hbS⟩ := Multiset.exists_mem_of_ne_zero hS0
        have hbrest : b ∈ rest := Multiset.mem_of_le hS_rest hbS
        have hab : a ≤ b := ha_le b hbrest
        have hS_eq : b ::ₘ (S.erase b) = S := Multiset.cons_erase hbS
        have hS'_le : S.erase b ≤ (rest : Multiset ℕ) := (Multiset.erase_le b S).trans hS_rest
        have hcard : Multiset.card S = Multiset.card (S.erase b) + 1 := by
          simpa [Multiset.card_cons] using congrArg Multiset.card hS_eq.symm
        conv_lhs => rw [hcard, List.take_succ_cons, List.sum_cons]
        conv_rhs => rw [← hS_eq, Multiset.sum_cons]
        exact Nat.add_le_add hab (sum_take_le_sum_of_le hrest hS'_le)

private lemma le_getLast_of_pairwise_lt :
    ∀ {L : List ℕ}, L.Pairwise (· < ·) → ∀ (hne : L ≠ []) {x : ℕ}, x ∈ L → x ≤ L.getLast hne
  | [], _, hne, _, _ => (hne rfl).elim
  | [a], _, _, x, hx => by
    simp only [List.mem_singleton] at hx
    simp [hx]
  | a :: b :: tail, hL, _, x, hx => by
    rw [List.pairwise_cons] at hL
    rw [List.mem_cons] at hx
    rw [List.getLast_cons (List.cons_ne_nil b tail)]
    rcases hx with rfl | hx'
    · exact (hL.1 _ (List.getLast_mem (List.cons_ne_nil b tail))).le
    · exact le_getLast_of_pairwise_lt hL.2 (List.cons_ne_nil b tail) hx'

omit [DecidableEq α] in
theorem annihilationNumberEq (G : SimpleGraph α) [DecidableRel G.Adj] :
    annihilationNumber G = annihilationNumber' G := by
  let L : List ℕ := (Finset.univ.val.map fun v => G.degree v).sort (· ≤ ·)
  let cond : ℕ → Bool := fun k => decide ((L.take k).sum ≤ (L.drop k).sum)
  let cands : List ℕ := (List.range (Fintype.card α + 1)).filter cond
  have hL_coe : (L : Multiset ℕ) = degreeMultiset G := by
    simp [L, degreeMultiset]
  have hL_len : L.length = Fintype.card α := by
    simp [L]
  have hL_sorted : L.Pairwise (· ≤ ·) :=
    Multiset.pairwise_sort (degreeMultiset G) (· ≤ ·)
  have hL_sum : L.sum = 2 * G.edgeFinset.card := by
    rw [← Multiset.sum_coe, hL_coe, degreeMultiset]
    exact G.sum_degrees_eq_twice_card_edges
  have hcond_iff : ∀ k : ℕ, cond k = true ↔ (L.take k).sum ≤ G.edgeFinset.card := by
    intro k
    have hsplit : (L.take k).sum + (L.drop k).sum = 2 * G.edgeFinset.card := by
      rw [← List.sum_append, List.take_append_drop, hL_sum]
    simp only [cond, decide_eq_true_eq]
    omega
  have hcands_ne : cands ≠ [] := by
    intro hnil
    have h0 : 0 ∈ cands := by
      rw [List.mem_filter]
      exact ⟨List.mem_range.mpr (Nat.zero_lt_succ _), (hcond_iff 0).mpr (by simp)⟩
    rw [hnil] at h0
    simp at h0
  have hgetLast : cands.getLast! = cands.getLast hcands_ne := by
    have aux : ∀ (l : List ℕ) (h : l ≠ []), l.getLast! = l.getLast h := by
      intro l h
      cases l with
      | nil => exact (h rfl).elim
      | cons a t => simp [List.getLast!]
    exact aux cands hcands_ne
  have hcands_sorted : cands.Pairwise (· < ·) :=
    List.pairwise_lt_range.filter cond
  change annihilationNumber G = cands.getLast!
  rw [hgetLast]
  apply le_antisymm
  · unfold annihilationNumber
    apply Finset.sup_le
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_Iic] at hS
    have hcard_le : Multiset.card S ≤ Fintype.card α := by
      calc Multiset.card S ≤ Multiset.card (degreeMultiset G) := Multiset.card_le_card hS.1
        _ = Fintype.card α := by simp [degreeMultiset]
    have hS_le_L : S ≤ (L : Multiset ℕ) := by
      rw [hL_coe]
      exact hS.1
    have hk_mem : Multiset.card S ∈ cands := by
      rw [List.mem_filter]
      refine ⟨List.mem_range.mpr (Nat.lt_succ_of_le hcard_le), ?_⟩
      exact (hcond_iff _).mpr ((sum_take_le_sum_of_le hL_sorted hS_le_L).trans hS.2)
    exact le_getLast_of_pairwise_lt hcands_sorted hcands_ne hk_mem
  · set k := cands.getLast hcands_ne
    have hk_mem : k ∈ cands := List.getLast_mem hcands_ne
    rw [List.mem_filter] at hk_mem
    have hk_le : k ≤ Fintype.card α := Nat.lt_succ_iff.mp (List.mem_range.mp hk_mem.1)
    have hk_sum : (L.take k).sum ≤ G.edgeFinset.card := (hcond_iff k).mp hk_mem.2
    let S : Multiset ℕ := (L.take k : List ℕ)
    have hS_le : S ≤ degreeMultiset G := by
      rw [← hL_coe]
      exact Multiset.coe_le.mpr (List.take_sublist k L).subperm
    have hS_mem : S ∈ (Finset.Iic (degreeMultiset G)).filter
        (fun T => Multiset.sum T ≤ G.edgeFinset.card) := by
      simp only [Finset.mem_filter, Finset.mem_Iic]
      exact ⟨hS_le, by simpa [S] using hk_sum⟩
    have hS_card : Multiset.card S = k := by
      simp [S, List.length_take, hL_len, hk_le]
    simpa [annihilationNumber, hS_card] using Finset.le_sup (f := Multiset.card) hS_mem

end SimpleGraph
