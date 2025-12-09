/-
Copyright 2025 The Formal Conjectures Authors.

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
import Batteries.Data.List.Lemmas
import Init.Data.List.OfFn
import Init.Data.Nat.Basic
import Init.Prelude
import Init.PropLemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Order.MinMax


open Classical

namespace Algebra.Group.GrowthRate

variable {G : Type} [Group G]

structure SymmetricGeneratingSet (S : Finset G) where
  h_inv: (∀ s ∈ S, s⁻¹ ∈ S)
  h_gen: Subgroup.closure ↑S = (⊤ : Subgroup G)

lemma symmetricFiniteGeneratingSetExists [h_FG : Group.FG G] :
  ∃ S : Finset G, SymmetricGeneratingSet S := by
    obtain ⟨ S, hS ⟩ := h_FG.out
    let S_inv : Finset G := S.image (·⁻¹)
    let S' : Finset G := S ∪ S_inv
    use S'
    constructor
    · intro s a
      simp_all only [S', S_inv, Finset.mem_union, Finset.mem_image]
      cases a with
      | inl hsS => right; simp only [inv_inj]; use s
      | inr hsS_inv =>
        left
        obtain ⟨ s', hs'S, hs_eq ⟩ := hsS_inv
        subst hs_eq; simp_all only [inv_inv]
    · have hSub : S ⊆ S' := Finset.subset_union_left
      have hClosure := @Subgroup.closure_mono G _ S S' hSub
      rw [hS] at hClosure
      exact top_le_iff.mp hClosure

def prodOfWord {n : ℕ} {S : Finset G} (w : Fin n → S) : G :=
  (List.ofFn (fun i => ↑(w i))).prod

lemma prodOfWord_product_left {n : ℕ} {S : Finset G} (w : Fin n.succ → S) :
  prodOfWord w = (↑(w 0)) * prodOfWord (Fin.tail w) := by
    rw [prodOfWord, prodOfWord]
    simp only [Nat.succ_eq_add_one, List.ofFn_succ, List.prod_cons, Fin.tail]

lemma prodOfWord_product_right {n : ℕ} {S : Finset G} (w : Fin n.succ → S) :
  prodOfWord w = prodOfWord (Fin.init w) * (↑(w (Fin.last n))) := by
  rw [prodOfWord, prodOfWord]
  rw [List.ofFn_succ' fun i ↦ (w i : G)]
  apply List.prod_concat

lemma prodOfWord_length_zero_is_one {S : Finset G} (w : Fin 0 → S) :
  prodOfWord w = (1 : G) := by
    rw [prodOfWord]
    simp only [List.ofFn_zero, List.prod_nil]

lemma prodOfWord_length_one_is_element {S : Finset G} (w : Fin 1 → S) :
  prodOfWord w ∈ S := by
    rw [prodOfWord]
    simp only [List.ofFn_succ, List.prod_cons]
    rw [←prodOfWord, prodOfWord_length_zero_is_one, mul_one]
    exact (w 0).2

noncomputable
def wordShell (S : Finset G) (n : ℕ) : Finset G :=
  let wordsOfLengthN : Finset (Fin n → S) := Finset.univ
  wordsOfLengthN.image (fun w ↦ prodOfWord w)

noncomputable
def wordBall (S : Finset G) (n : ℕ) : Finset G :=
  (Finset.range (n + 1)).biUnion (wordShell S ·)

lemma shell_subset_ball (S : Finset G) {m n : ℕ} (hmn : m ≤ n) :
  wordShell S m ⊆ wordBall S n := by
    rw [wordBall]
    intro g hg
    simp_all only [Finset.mem_biUnion, Finset.mem_range]
    use m; exact ⟨Nat.lt_add_one_of_le hmn, hg⟩

lemma wordShell_element_is_word_product (S : Finset G) (n : ℕ) :
  ∀ a ∈ wordShell S n, ∃ w : Fin n → S,
  a = prodOfWord w := by
    intro a ha
    rw [wordShell] at ha
    simp only [Finset.mem_image] at ha
    obtain ⟨ w, hw_univ, ha_eq ⟩ := ha
    use w; apply Eq.symm; exact ha_eq

lemma wordBall_element_is_wordShell_element (S : Finset G) (n : ℕ) :
  ∀ a ∈ wordBall S n, ∃ k ≤ n, a ∈ wordShell S k := by
    intro a ha
    rw [wordBall] at ha
    simp only [Finset.mem_biUnion, Finset.mem_range] at ha
    obtain ⟨ k, hk_n, ha_in_shell ⟩ := ha
    use k
    constructor
    · exact Nat.le_of_lt_succ hk_n
    · exact ha_in_shell

lemma wordBall_element_is_word_product (S : Finset G) (n : ℕ) :
  ∀ a ∈ wordBall S n, ∃ k ≤ n, ∃ w : Fin k → S,
  a = prodOfWord w := by
    intro a ha
    have h_wordShell := wordBall_element_is_wordShell_element S n a ha
    obtain ⟨ k, hk_n, ha_in_shell ⟩ := h_wordShell
    have h_word := wordShell_element_is_word_product S k a ha_in_shell
    use k

lemma word_product_is_in_wordShell (S : Finset G) {n : ℕ} (w : Fin n → S) :
  prodOfWord w ∈ wordShell S n := by
    rw [wordShell]
    simp only [Finset.mem_image]
    use w
    simp only [Finset.mem_univ, and_self]

lemma word_product_is_in_wordBall (S : Finset G) (n : ℕ) (w : Fin n → S) :
  prodOfWord w ∈ wordBall S n := by
    have hShell : prodOfWord w ∈ wordShell S n := by
      exact word_product_is_in_wordShell S w
    exact shell_subset_ball S (le_refl n) hShell

lemma wordShell_zero_eq_one (S : Finset G) :
  wordShell S 0 = {1} := by
    rfl

lemma wordShell_zero_element_eq_one (S : Finset G) :
  ∀ a ∈ wordShell S 0, a = 1 := by
    intro a ha
    rw [wordShell_zero_eq_one S, Finset.mem_singleton] at ha
    exact ha

lemma wordBall_zero_eq_one (S : Finset G) :
  wordBall S 0 = {1} := by
    rfl

lemma wordBall_zero_element_eq_one (S : Finset G) :
  ∀ a ∈ wordBall S 0, a = 1 := by
    intro a ha
    rw [wordBall_zero_eq_one S, Finset.mem_singleton] at ha
    exact ha

lemma wordBall_is_wordBall_union_wordShell (S : Finset G) (n : ℕ) :
  wordBall S (n + 1) = wordBall S n ∪ wordShell S (n + 1) := by
    rw [wordBall]
    rw [Finset.range_succ, Finset.biUnion_insert]
    apply Finset.union_comm

lemma wordBall_n_subset_wordBall_n_plus_one (S : Finset G) (n : ℕ) :
  wordBall S n ⊆ wordBall S (n + 1) := by
    have h : Finset.range (n + 1) ⊆ Finset.range (n + 1 + 1) := by
      simp only [Finset.range_subset, Nat.le_add_right]
    exact Finset.biUnion_subset_biUnion_of_subset_left (fun x ↦ wordShell S x) h

lemma wordBall_monotone (S : Finset G) {m n : ℕ} (hmn : m ≤ n) :
  wordBall S m ⊆ wordBall S n := by
    have hmn' : ∃ k : ℕ, n = m + k := Nat.exists_eq_add_of_le hmn
    obtain ⟨ k, hk ⟩ := hmn'
    subst hk
    induction k with
    | zero => rfl
    | succ n ih =>
      have subset_mn1 := wordBall_n_subset_wordBall_n_plus_one S (m + n)
      simp_all only [Nat.le_add_right, forall_const]
      exact Set.Subset.trans ih subset_mn1

lemma wordBall_contains_one (S : Finset G) (n : ℕ) :
  (1 : G) ∈ wordBall S n := by
    have h_one_in_ball_zero : (1 : G) ∈ wordBall S 0 := by
      simp_all only [wordBall_zero_eq_one S, Finset.mem_singleton]
    exact wordBall_monotone S (Nat.zero_le n) h_one_in_ball_zero

lemma wordShell_one_eq_S (S : Finset G) :
  wordShell S 1 = S := by
    ext g
    constructor
    · intro hg
      obtain ⟨ w, hw_eq ⟩ := wordShell_element_is_word_product S 1 g hg
      subst hw_eq
      apply prodOfWord_length_one_is_element w
    · intro hgS
      let w_g : Fin 1 → S := fun _ ↦ ⟨ g, hgS ⟩
      have h_prod : g = prodOfWord w_g := by
        rw [prodOfWord]
        simp only [List.ofFn_succ, List.prod_cons]
        rw [←prodOfWord, prodOfWord_length_zero_is_one, mul_one]
      rw [h_prod]
      exact word_product_is_in_wordShell S w_g

lemma wordBall_one_eq_S_union_one (S : Finset G) :
  wordBall S 1 = S ∪ {1} := by
    have h_union := wordBall_is_wordBall_union_wordShell S 0
    rw [zero_add, wordBall_zero_eq_one S, wordShell_one_eq_S S, Finset.union_comm] at h_union
    exact h_union

lemma wordShell_element_is_product_left (S : Finset G) (n : ℕ) :
  ∀ a ∈ wordShell S (n + 1), ∃ s ∈ S, ∃ a' ∈ wordShell S n,
  a = s * a' := by
    intro a ha
    rw [wordShell, Finset.mem_image] at ha
    obtain ⟨ f, hf1, hProd ⟩ := ha
    rw [prodOfWord_product_left] at hProd
    use (f 0 : S)
    constructor
    · simp only [Finset.coe_mem]
    · let a' : G := prodOfWord (Fin.tail f); use a'
      constructor
      · exact word_product_is_in_wordShell S (Fin.tail f)
      · rw [hProd]

lemma wordShell_mul_element_left (S : Finset G) (n : ℕ) :
  ∀ a ∈ wordShell S n, ∀ s ∈ S, s * a ∈ wordShell S (n + 1) := by
    intro a h_a s h_s
    rw [wordShell, Finset.mem_image] at ⊢ h_a
    simp_all only [prodOfWord_product_left, Finset.mem_univ, true_and]
    obtain ⟨ w, h_prod ⟩ := h_a
    let w' := Matrix.vecCons ⟨s, h_s⟩ w; use w'
    have h_head : (w' 0 = ⟨s, h_s⟩) := by
      rfl
    have h_tail : prodOfWord (Fin.tail w') = a := by
      subst h_prod
      rfl
    rw [h_head, h_tail]

lemma wordShell_mul_wordShell (S : Finset G) (k n : ℕ) :
  ∀ a ∈ wordShell S k, ∀ a' ∈ wordShell S n, a * a' ∈ wordShell S (k + n) := by
    induction k with
    | zero =>
      intro a ha a' ha'
      rw [zero_add]
      have ha_one : a = (1 : G) := wordShell_zero_element_eq_one S a ha
      rw [ha_one, one_mul]
      exact ha'
    | succ k ih =>
      intro a ha a' ha'
      obtain ⟨ s, hsS, a_k, ha_k, ha_eq_prod ⟩ := wordShell_element_is_product_left S k a ha
      subst ha_eq_prod
      have h_prod_in_k_plus_n : a_k * a' ∈ wordShell S (k + n) := ih a_k ha_k a' ha'
      have move_plus_one : k + 1 + n = (k + n) + 1 := by
        rw [Nat.add_assoc, Nat.add_comm 1 n, ←Nat.add_assoc]
      rw [mul_assoc, move_plus_one]
      exact wordShell_mul_element_left S (k + n) (a_k * a') h_prod_in_k_plus_n s hsS

lemma wordBall_mul_wordBall (S : Finset G) (k n : ℕ) :
  ∀ a ∈ wordBall S k, ∀ a' ∈ wordBall S n, a * a' ∈ wordBall S (k + n) := by
    intro a ha a' ha'
    obtain ⟨ k', hk', ha_in_shell ⟩ := wordBall_element_is_wordShell_element S k a ha
    obtain ⟨ n', hn', ha'_in_shell ⟩ := wordBall_element_is_wordShell_element S n a' ha'
    have h_le : k' + n' ≤ k + n := Nat.add_le_add hk' hn'
    have h_prod_in_shell : a * a' ∈ wordShell S (k' + n') :=
      wordShell_mul_wordShell S k' n' a ha_in_shell a' ha'_in_shell
    exact shell_subset_ball S h_le h_prod_in_shell

lemma element_wordBall_product_in_wordBall (S : Finset G) (n : ℕ) :
  ∀ s ∈ S, ∀ a ∈ wordBall S n, s * a ∈ wordBall S (n + 1) := by
    intro s hsS a ha
    have hs_ball : s ∈ wordBall S 1 := by
      rw [wordBall_one_eq_S_union_one S]
      exact Finset.mem_union_left _ hsS
    rw [add_comm]
    exact wordBall_mul_wordBall S 1 n s hs_ball a ha

lemma wordBall_element_is_product_left (S : Finset G) (n : ℕ) :
  ∀ a ∈ wordBall S (n + 1), a = 1 ∨ ∃ s ∈ S, ∃ a' ∈ wordBall S n,
  a = s * a' := by
    intro a ha
    obtain ⟨ m, hm, ha ⟩ := wordBall_element_is_wordShell_element S (n + 1) a ha
    cases m with
    | zero => left; exact wordShell_zero_element_eq_one S a ha
    | succ m' =>
      right
      obtain ⟨ s, hsS, a', ha', ha_eq ⟩ := wordShell_element_is_product_left S m' a ha
      use s, hsS, a', shell_subset_ball S (Nat.le_of_lt_succ hm) ha'

lemma wordShell_product (S : Finset G) (k n : ℕ) :
  ∀ a ∈ wordShell S (k + n), ∃ aₖ ∈ wordShell S k, ∃ aₙ ∈ wordShell S n,
  a = aₖ * aₙ := by
    induction k with
    | zero =>
      intro a ha; rw [zero_add] at ha
      use 1
      rw [wordShell_zero_eq_one S]
      simp only [Finset.mem_singleton, true_and, one_mul]
      use a, ha
    | succ k ih =>
      intro a ha
      rw [add_assoc, add_comm 1 n, ←add_assoc] at ha
      obtain ⟨ s, hsS, a', ha', ha_eq ⟩ := wordShell_element_is_product_left S (k + n) a ha
      obtain ⟨ aₖ, haₖ, aₙ, haₙ, ha'_eq ⟩ := ih a' ha'
      use (s * aₖ),  wordShell_mul_element_left S k aₖ haₖ s hsS
      use aₙ, haₙ
      rw [ha_eq, ha'_eq, mul_assoc]

lemma wordBall_element_is_product (S : Finset G) (k n : ℕ) :
  ∀ a ∈ wordBall S (k + n), ∃ aₖ ∈ wordBall S k, ∃ aₙ ∈ wordBall S n,
  a = aₖ * aₙ := by
    intro a ha
    obtain ⟨ m, hm, ha_in_shell ⟩ := wordBall_element_is_wordShell_element S (k + n) a ha

    have h_sum : ∃ k' n' : ℕ, m = k' + n' ∧ k' ≤ k ∧ n' ≤ n := by
      cases Nat.le_total m k with
      | inl h_m_le_k =>
        use m, 0
        simp_all only [add_zero, Nat.zero_le, and_self]
      | inr h_k_le_m =>
        let diff := m - k; use k, diff
        simp_all only [Nat.add_sub_cancel', le_refl, true_and, Nat.sub_le_iff_le_add, diff,
          add_comm]

    obtain ⟨ k', n', h_m_eq, h_k'_le_k, h_n'_le_n ⟩ := h_sum
    rw [h_m_eq] at ha_in_shell
    obtain ⟨ a_k', ha_k' , a_n', ha_n', ha_eq ⟩ := wordShell_product S k' n' a ha_in_shell

    have h_a_k'_in_ball : a_k' ∈ wordBall S k := shell_subset_ball S h_k'_le_k ha_k'
    have h_a_n'_in_ball : a_n' ∈ wordBall S n := shell_subset_ball S h_n'_le_n ha_n'

    use a_k', h_a_k'_in_ball, a_n', h_a_n'_in_ball, ha_eq

lemma wordShell_closed_under_inv (S : Finset G) (hS : SymmetricGeneratingSet S) :
  ∀ n : ℕ, ∀ a ∈ wordShell S n, a⁻¹ ∈ wordShell S n := by
    intro n
    induction n with
    | zero =>
      intro a ha
      rw [wordShell_zero_eq_one S] at ha ⊢
      simp_all only [Finset.mem_singleton, inv_one]
    | succ n ih =>
      intro a ha
      obtain ⟨ s, hsS, a', ha', ha_eq ⟩ := wordShell_element_is_product_left S n a ha
      have h_a_inv_eq : a⁻¹ = a'⁻¹ * s⁻¹ := by
        rw [ha_eq, mul_inv_rev]
      have h_a'_inv_in_shell : a'⁻¹ ∈ wordShell S n := by
        exact ih a' ha'
      have h_s_inv_in_S : s⁻¹ ∈ wordShell S 1 := by
        rw [wordShell_one_eq_S S]
        exact hS.h_inv s hsS
      rw [h_a_inv_eq]
      exact wordShell_mul_wordShell S n 1 a'⁻¹ h_a'_inv_in_shell s⁻¹ h_s_inv_in_S

lemma wordBall_closed_under_inv (S : Finset G) (hS : SymmetricGeneratingSet S) :
  ∀ n : ℕ, ∀ a ∈ wordBall S n, a⁻¹ ∈ wordBall S n := by
    intro n a ha
    obtain ⟨ k, hk, ha_in_shell ⟩ := wordBall_element_is_wordShell_element S n a ha
    have h_inv_in_shell := wordShell_closed_under_inv S hS k a ha_in_shell
    exact shell_subset_ball S hk h_inv_in_shell

def allBalls (S : Finset G) : Set G :=
  ⋃ n : ℕ, wordBall S n

def in_allBalls (S : Finset G) (g : G) (_hg : g ∈ Subgroup.closure S) : Prop :=
  g ∈ allBalls S

lemma allBalls_mem (S : Finset G) :
  ∀ (g : G) (hg : g ∈ S), in_allBalls S g (Subgroup.subset_closure hg) := by
    intro g hg
    rw [in_allBalls, allBalls, Set.mem_iUnion]
    use 1
    exact wordBall_one_eq_S_union_one S ▸ Finset.mem_union_left _ hg

lemma allBalls_one (S : Finset G) :
  in_allBalls S (1 : G) (Subgroup.one_mem ((Subgroup.closure S) : Subgroup G)) := by
    rw [in_allBalls, allBalls, Set.mem_iUnion]
    use 0
    exact wordBall_contains_one S 0

lemma allBalls_mul (S : Finset G) :
  ∀ (x y : G)
    (hx : x ∈ (Subgroup.closure S : Subgroup G))
    (hy : y ∈ (Subgroup.closure S : Subgroup G)),
    (in_allBalls S x hx) → (in_allBalls S y hy) →
    (in_allBalls S (x * y) (Subgroup.mul_mem ((Subgroup.closure S) : Subgroup G) hx hy)) := by
    intro x y _hx_closure _hy_closure hx hy
    rw [in_allBalls, allBalls, Set.mem_iUnion] at hx hy ⊢
    obtain ⟨ n_x, hn_x ⟩ := hx
    obtain ⟨ n_y, hn_y ⟩ := hy
    use n_x + n_y
    exact wordBall_mul_wordBall S n_x n_y x hn_x y hn_y

lemma allBalls_inv (S : Finset G) (hS : SymmetricGeneratingSet S) :
  ∀ (g : G) (hg : g ∈ (Subgroup.closure S : Subgroup G)), (in_allBalls S g hg) →
  (in_allBalls S g⁻¹ (Subgroup.inv_mem (Subgroup.closure S : Subgroup G) hg)) := by
    intro g _hg_closure hx
    rw [in_allBalls, allBalls, Set.mem_iUnion] at hx ⊢
    obtain ⟨ n, hn ⟩ := hx
    exact ⟨n, wordBall_closed_under_inv S hS n g hn⟩

lemma mem_top_carrier :
  ∀ g : G, g ∈ (⊤ : Subgroup G).carrier := by
    intro g
    simp only [Subgroup.top_toSubmonoid, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
      Submonoid.mem_top]

theorem allBalls_cover_G {S : Finset G} (hS : SymmetricGeneratingSet S) :
  allBalls S = (⊤ : Subgroup G).carrier := by
    ext g
    constructor
    · simp only [mem_top_carrier, implies_true]
    · intro hg
      have h_gen := hS.h_gen
      have h_union_closure : (Subgroup.closure (S : Set G)).carrier ⊆ allBalls S := by
        intro g' hg'
        let p := in_allBalls S
        exact @Subgroup.closure_induction G _ S p
          (allBalls_mem S) (allBalls_one S) (allBalls_mul S) (allBalls_inv S hS) g' hg'
      rw [←h_gen] at hg
      exact Set.mem_of_subset_of_mem h_union_closure hg

lemma mem_allBalls {S : Finset G} (hS : SymmetricGeneratingSet S) (g : G) :
  g ∈ allBalls S := by
    rw [allBalls_cover_G hS]
    simp only [mem_top_carrier]

lemma g_in_ball {S : Finset G} (hS : SymmetricGeneratingSet S) :
  ∀ g : G, ∃ n : ℕ, g ∈ wordBall S n := by
    intro g
    have h_g_in_allBalls := mem_allBalls hS g
    rw [allBalls, Set.mem_iUnion] at h_g_in_allBalls
    exact h_g_in_allBalls

lemma finset_subset_wordBall (S S' : Finset G) (hS : SymmetricGeneratingSet S') :
  ∃ C : ℕ, S ⊆ wordBall S' C := by
    let f_C : G → ℕ := fun g ↦ Nat.find (g_in_ball hS g)
    let C := S.sup f_C; use C
    intro s hs
    have hf_C : ∀ g : G, g ∈ wordBall S' (f_C g) := fun g => Nat.find_spec (g_in_ball hS g)
    exact wordBall_monotone S' (Finset.le_sup hs) (hf_C s)

lemma wordBall_subset_scaled_wordBall (S S' : Finset G) (hS' : SymmetricGeneratingSet S') :
  ∃ C : ℕ, ∀ n : ℕ, wordBall S n ⊆ wordBall S' (C * n) := by
    obtain ⟨ C, hC ⟩ := finset_subset_wordBall S S' hS'
    use C
    intro n
    induction n with
    | zero =>
      simp only [Nat.mul_zero, wordBall_zero_eq_one, Finset.singleton_subset_iff,
        Finset.mem_singleton]
    | succ n ih =>
      intro g hg
      obtain h_cases := wordBall_element_is_product_left S n g hg
      cases h_cases with
      | inl h_eq_one =>
        subst h_eq_one
        exact wordBall_contains_one S' (C * (n + 1))
      | inr h_prod =>
        obtain ⟨s, hsS, a', ha', ha_eq⟩ := h_prod
        have h_s_in_C_ball := hC hsS
        have h_a'_in_Cn_ball := ih ha'
        have h_prod_in_C_plus_Cn_ball :=
          wordBall_mul_wordBall S' C (C * n) s h_s_in_C_ball a' h_a'_in_Cn_ball
        have distribute_plus_one : C * (n + 1) = C + C * n := by
          rw [Nat.mul_succ, Nat.add_comm]
        rw [distribute_plus_one]
        subst ha_eq; exact h_prod_in_C_plus_Cn_ball

lemma wordBall_subset_scaled_wordBall_succ (S S' : Finset G) (hS' : SymmetricGeneratingSet S') :
  ∃ C : ℕ, C > 0 ∧ ∀ n : ℕ, wordBall S n ⊆ wordBall S' (C * n) := by
    obtain ⟨ C, hC ⟩ := wordBall_subset_scaled_wordBall S S' hS'
    use C + 1, Nat.succ_pos C
    intro n
    have h_mul : C * n ≤ (C + 1) * n := by
      rw [Nat.add_one_mul]
      exact Nat.le_add_right (C * n) n
    specialize hC n
    have h_sub := wordBall_monotone S' h_mul
    exact Finset.Subset.trans hC h_sub

noncomputable
def growthRate_of_wordBalls (S : Finset G) : ℕ → ℝ :=
  fun n => (wordBall S n).card

def GrowthLE (f g : ℕ → ℝ) : Prop :=
  ∃ C : ℕ, C > 0 ∧ ∀ᶠ n in Filter.atTop, f n ≤ g (C * n)

def GrowthEquiv (f g : ℕ → ℝ) : Prop :=
  GrowthLE f g ∧ GrowthLE g f

def GrowsLike (G : Type) [Group G] (f : ℕ → ℝ) : Prop :=
  ∃ (S : Finset G), SymmetricGeneratingSet S ∧ GrowthEquiv (growthRate_of_wordBalls S) f

lemma GrowthLE.refl {f : ℕ → ℝ} : GrowthLE f f := by
  unfold GrowthLE
  use 1, Nat.one_pos
  filter_upwards
  intro n
  rw [Nat.one_mul]

lemma GrowthLE.trans {f g h : ℕ → ℝ} (h_fg : GrowthLE f g) (h_gh : GrowthLE g h) :
    GrowthLE f h := by
  unfold GrowthLE at h_fg h_gh ⊢
  obtain ⟨ Cf, hCf, hev_f ⟩ := h_fg
  obtain ⟨ Cg, hCg, hev_g ⟩ := h_gh
  use Cg * Cf, Nat.mul_pos hCg hCf

  rw [Filter.eventually_atTop] at hev_f hev_g ⊢
  obtain ⟨N_f, hN_f⟩ := hev_f
  obtain ⟨N_g, hN_g⟩ := hev_g

  use Nat.max N_f N_g
  intro N hN
  have hN_f_bound : N_f ≤ N := le_of_max_le_left hN
  have hN_g_bound : N_g ≤ N := le_of_max_le_right hN
  have hN_g_scaled : N_g ≤ Cf * N := le_trans hN_g_bound (Nat.le_mul_of_pos_left N hCf)

  calc f N
    _ ≤ g (Cf * N) := hN_f N hN_f_bound
    _ ≤ h (Cg * (Cf * N)) := hN_g (Cf * N) hN_g_scaled
    _ = h (Cg * Cf * N) := by rw [mul_assoc]

lemma GrowthEquiv.symm {f g : ℕ → ℝ} (h_fg : GrowthEquiv f g) : GrowthEquiv g f := by
  exact And.intro h_fg.2 h_fg.1

lemma GrowthEquiv.refl (f : ℕ → ℝ) : GrowthEquiv f f := by
  exact And.intro GrowthLE.refl GrowthLE.refl

lemma GrowthEquiv.trans {f g h : ℕ → ℝ} (h_fg : GrowthEquiv f g) (h_gh : GrowthEquiv g h) :
    GrowthEquiv f h := by
    exact ⟨GrowthLE.trans h_fg.1 h_gh.1, GrowthLE.trans h_gh.2 h_fg.2⟩

instance GrowthEquivSetoid : Setoid (ℕ → ℝ) where
  r := GrowthEquiv
  iseqv := ⟨GrowthEquiv.refl, GrowthEquiv.symm, GrowthEquiv.trans⟩

abbrev GrowthClass : Type := Quotient GrowthEquivSetoid

noncomputable
def growthRateClass_of_wordBalls {G : Type} [Group G] (S : Finset G) : GrowthClass :=
  Quotient.mk GrowthEquivSetoid (growthRate_of_wordBalls S)

noncomputable
def growthRate (G : Type) [Group G] [Group.FG G] : GrowthClass :=
  let S := Classical.choose symmetricFiniteGeneratingSetExists
  @growthRateClass_of_wordBalls G _ S

lemma GrowthLE.of_equiv_left {f f' g : ℕ → ℝ} (hff' : GrowthEquiv f f') (hfg : GrowthLE f g) :
    GrowthLE f' g := by
  exact GrowthLE.trans hff'.2 hfg

lemma GrowthLE.of_equiv_right {f g g' : ℕ → ℝ} (hgg' : GrowthEquiv g g') (hfg : GrowthLE f g) :
    GrowthLE f g' := by
  exact GrowthLE.trans hfg hgg'.1

instance : LE GrowthClass where
  le := Quotient.lift₂ GrowthLE (by
    intro f g f' g' hff' hgg'
    simp only [eq_iff_iff]
    constructor
    · intro h
      exact GrowthLE.of_equiv_left hff' (GrowthLE.of_equiv_right hgg' h)
    · intro h
      exact GrowthLE.of_equiv_left (GrowthEquiv.symm hff') (GrowthLE.of_equiv_right (GrowthEquiv.symm hgg') h))

lemma growthRatesLE (f g : ℕ → ℝ) : GrowsLike G f → GrowsLike G g → GrowthLE f g := by
    intro h_f h_g
    obtain ⟨ S_f, hS_f, h_equiv_f ⟩ := h_f
    obtain ⟨ S_g, hS_g, h_equiv_g ⟩ := h_g
    unfold GrowthEquiv at h_equiv_f h_equiv_g
    unfold GrowthLE at h_equiv_f h_equiv_g
    unfold growthRate_of_wordBalls at h_equiv_f h_equiv_g

    obtain ⟨ C_f2, hC_f2_pos, h_f_ubound_ev ⟩ := h_equiv_f.2
    obtain ⟨ C_g1, hC_g1_pos, h_g_lbound_ev ⟩ := h_equiv_g.1
    obtain ⟨ N_f, h_f_ubound ⟩ := Filter.eventually_atTop.mp h_f_ubound_ev
    obtain ⟨ N_g, h_g_lbound ⟩ := Filter.eventually_atTop.mp h_g_lbound_ev

    obtain ⟨ C₁, hC₁ ⟩ := wordBall_subset_scaled_wordBall_succ S_f S_g hS_g
    have hC₁_pos : C₁ > 0 := hC₁.1
    have hC₁_bound := hC₁.2

    let E₁ := C_g1 * C₁ * C_f2
    unfold GrowthLE
    have hE₁_pos : E₁ > 0 := Nat.mul_pos (Nat.mul_pos hC_g1_pos hC₁_pos) hC_f2_pos
    use E₁, hE₁_pos
    apply Filter.eventually_atTop.mpr

    use max N_f N_g; intro N hN
    have h_Nf_bound : N_f ≤ N := le_of_max_le_left hN
    have h_Ng_bound : N_g ≤ N := le_of_max_le_right hN

    have h_f1 : f N ≤ (wordBall S_f (C_f2 * N)).card := by
      exact h_f_ubound N h_Nf_bound
    have h_f2 : (wordBall S_f (C_f2 * N)).card ≤ (wordBall S_g (C₁ * C_f2 * N)).card := by
      apply Finset.card_le_card
      rw [mul_assoc]
      exact hC₁_bound (C_f2 * N)
    have h_f3 : (wordBall S_g (C₁ * C_f2 * N)).card ≤ g ((C_g1 * C₁ * C_f2) * N) := by
      have h_prod : (C_g1 * (C₁ * C_f2 * N)) = (C_g1 * C₁ * C_f2 * N) := by
        rw [mul_assoc, mul_assoc, mul_assoc]
      rw [←h_prod]
      apply h_g_lbound (C₁ * C_f2 * N)
      have h_mul : C₁ * C_f2 ≥ 1 := by
        exact Right.one_le_mul hC₁_pos hC_f2_pos
      have h_mul_n : C₁ * C_f2 * N ≥ N := by
        exact Nat.le_mul_of_pos_left N h_mul
      exact Nat.le_trans h_Ng_bound h_mul_n
    calc f N
      _ ≤ (wordBall S_f (C_f2 * N)).card := h_f1
      _ ≤ (wordBall S_g (C₁ * C_f2 * N)).card := by exact_mod_cast h_f2
      _ ≤ g ((C_g1 * C₁ * C_f2) * N) := h_f3

theorem growthRatesEquiv (f g : ℕ → ℝ) : GrowsLike G f → GrowsLike G g → GrowthEquiv f g := by
  intro h_f h_g
  constructor
  · apply growthRatesLE f g h_f h_g
  · apply growthRatesLE g f h_g h_f

theorem growthRate_well_defined (G : Type) [Group G] [Group.FG G]
    (S S' : Finset G) (hS : @SymmetricGeneratingSet G _ S) (hS' : @SymmetricGeneratingSet G _ S') :
    growthRateClass_of_wordBalls S = growthRateClass_of_wordBalls S' := by
  apply Quotient.sound
  have h_growth_S : GrowsLike G (growthRate_of_wordBalls S) := by
    use S, hS
    exact GrowthEquiv.refl (growthRate_of_wordBalls S)
  have h_growth_S' : GrowsLike G (growthRate_of_wordBalls S') := by
    use S', hS'
    exact GrowthEquiv.refl (growthRate_of_wordBalls S')
  exact growthRatesEquiv (growthRate_of_wordBalls S) (growthRate_of_wordBalls S')
    h_growth_S h_growth_S'


/--
Some other maybe-useful lemmas that I proved but didn't use above:
-/

lemma wordShell_subset_H (S : Finset G) (H : Subgroup G) (hS : (S : Set G) ⊆ H.carrier) :
  ∀ n : ℕ, (wordShell S n : Set G) ⊆ H.carrier := by
    intro n
    induction n with
    | zero =>
      simp [wordShell, prodOfWord]
    | succ n ih =>
      intro g hg
      rw [wordShell] at hg
      obtain ⟨ s, hsS, w', hw', hw_eq ⟩ := wordShell_element_is_product_left S n g hg
      have hw'_H : w' ∈ H.carrier := ih hw'
      subst hw_eq
      simp_all only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid,
        Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      obtain ⟨w, h⟩ := hg
      apply MulMemClass.mul_mem
      · apply hS
        exact hsS
      · exact hw'_H

lemma wordBall_subset_H (S : Finset G) (H : Subgroup G) (hS : (S : Set G) ⊆ H.carrier) :
  ∀ n : ℕ, (wordBall S n : Set G) ⊆ H.carrier := by
    intro n
    rw [wordBall]
    intro g hg
    obtain ⟨ k, hk, hg_eq ⟩ := Finset.mem_biUnion.mp hg
    have hNShell_H : (wordShell S k : Set G) ⊆ H.carrier := wordShell_subset_H S H hS k
    exact hNShell_H hg_eq

lemma wordShell_card_bound (S : Finset G) (n : ℕ) :
  (wordShell S n).card ≤ (S.card) ^ n := by
    rw [wordShell]
    let h_words : Finset (Fin n → S) := Finset.univ
    have h_image_card : (h_words.image (fun w ↦ prodOfWord w)).card ≤ h_words.card := by
      apply Finset.card_image_le
    have h_words_card : h_words.card = (S.card) ^ n := by
      rw [Finset.card_univ, Fintype.card_pi, Fintype.card_coe, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    subst h_words
    rw [h_words_card] at h_image_card
    exact h_image_card

lemma wordShell_card_bound_prod (S : Finset G) (n m : ℕ) :
  (wordShell S (n + m)).card ≤ (S.card) ^ n * (wordShell S m).card := by
    have h_surj : wordShell S (n + m) ⊆
        (wordShell S n ×ˢ wordShell S m).image (fun ⟨wₙ, wₘ⟩ ↦ wₙ * wₘ) := by
      intro w hw
      obtain ⟨wₙ, hwₙ, wₘ, hwₘ, hw_eq⟩ := wordShell_product S n m w hw
      simp only [Finset.mem_image, Finset.mem_product]
      use (wₙ, wₘ)
      subst hw_eq
      simp_all only [and_self]
    have h_subset_card : (wordShell S (n + m)).card ≤
        ((wordShell S n ×ˢ wordShell S m).image (fun ⟨wₙ, wₘ⟩ ↦ wₙ * wₘ)).card := by
      apply Finset.card_le_card
      exact h_surj
    have h_image_card : ((wordShell S n ×ˢ wordShell S m).image (fun ⟨wₙ, wₘ⟩ ↦ wₙ * wₘ)).card
        ≤ (wordShell S n ×ˢ wordShell S m).card := Finset.card_image_le
    have h_product_card : (wordShell S n ×ˢ wordShell S m).card =
        (wordShell S n).card * (wordShell S m).card := by apply Finset.card_product
    have h_shell_bound_prod : (wordShell S n).card * (wordShell S m).card
        ≤ S.card ^ n * (wordShell S m).card := by
      have h_shell_bound := wordShell_card_bound S n
      exact Nat.mul_le_mul_right (wordShell S m).card h_shell_bound
    calc (wordShell S (n + m)).card
       _ ≤ ((wordShell S n ×ˢ wordShell S m).image (fun ⟨wₙ, wₘ⟩ ↦ wₙ * wₘ)).card := h_subset_card
       _ ≤ (wordShell S n ×ˢ wordShell S m).card := h_image_card
       _ = (wordShell S n).card * (wordShell S m).card := h_product_card
       _ ≤ S.card ^ n * (wordShell S m).card := h_shell_bound_prod

end Algebra.Group.GrowthRate
