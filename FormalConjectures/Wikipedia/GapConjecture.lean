import Init.Prelude
import Init.PropLemmas
import Mathlib.Data.Finset.Card
import Batteries.Data.List.Lemmas
import Init.Data.List.OfFn
import Init.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Union
import Mathlib.GroupTheory.Finiteness
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Basic


open Classical

variable {G : Type} [Group G]

def FiniteGeneratingSet (S : Finset G) : Prop :=
  Subgroup.closure ↑S = (⊤ : Subgroup G)

structure SymmetricFiniteGeneratingSet (S : Finset G) where
  h_inv: (∀ s ∈ S, s⁻¹ ∈ S)
  h_gen: FiniteGeneratingSet S

lemma symmetricFiniteGeneratingSetExists {G : Type} [hG : Group G] [h_FG : Group.FG G] :
  ∃ S : Finset G, SymmetricFiniteGeneratingSet S := by
    obtain ⟨ S, hS ⟩ := h_FG.out
    let S_inv : Finset G := S.image (·⁻¹)
    let S' : Finset G := S ∪ S_inv
    use S'
    constructor
    · aesop
    · have hSub : S ⊆ S' := by
        apply Finset.subset_union_left
      have hClosure := @Subgroup.closure_mono G hG S S' hSub
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
  have h : List.ofFn (fun i ↦ (w i : G)) = (List.ofFn fun i ↦ ↑(Fin.init w i)).concat (↑(w (Fin.last n))) := by
    exact List.ofFn_succ' fun i ↦ (w i : G)
  rw [h]
  apply List.prod_concat

noncomputable
def wordNShell (S : Finset G) (n : ℕ) : Finset G :=
  let wordsOfLength_n : Finset (Fin n → S) := Finset.univ
  wordsOfLength_n.image (fun w ↦ prodOfWord w)

noncomputable
def wordNBall (S : Finset G) (n : ℕ) : Finset G :=
  (Finset.range (n + 1)).biUnion (wordNShell S ·)

-- This is LLM generated, see if it can be tidied
lemma wordNBall_member_is_word (S : Finset G) (n : ℕ) :
  ∀ a ∈ wordNBall S n, ∃ k ≤ n, ∃ w : Fin k → S,
  a = prodOfWord w := by
    intro a ha
    rw [wordNBall] at ha
    simp only [Finset.mem_biUnion, Finset.mem_range] at ha
    obtain ⟨ k, hk_n, ha_in_shell ⟩ := ha
    rw [wordNShell] at ha_in_shell
    simp only [Finset.mem_image] at ha_in_shell
    obtain ⟨ w, hw_univ, ha_eq ⟩ := ha_in_shell
    use k
    constructor
    · exact Nat.le_of_lt_succ hk_n
    · use w
      apply Eq.symm
      exact ha_eq

-- This is LLM generated, see if it can be tidied
lemma word_is_in_wordNBall (S : Finset G) (n : ℕ) (w : Fin n → S) :
  prodOfWord w ∈ wordNBall S n := by
    rw [wordNBall]
    simp only [Finset.mem_biUnion, Finset.mem_range]
    use n
    constructor
    · simp
    · rw [wordNShell]
      simp only [Finset.mem_image]
      use w
      simp

lemma wordNShell_zero_eq_one (S : Finset G) :
  wordNShell S 0 = {1} := by
    rfl

lemma wordNBall_zero_eq_one (S : Finset G) :
  wordNBall S 0 = {1} := by
    rfl

lemma wordNPlus1Ball_union_WordNBall_WordNPlus1Shell (S : Finset G) (n : ℕ) :
  wordNBall S (n + 1) = wordNBall S n ∪ wordNShell S (n + 1) := by
    simp_all [wordNBall]
    rw [Finset.range_succ]
    rw [Finset.biUnion_insert]
    apply Finset.union_comm

lemma wordNBall_subset_wordNPlus1Ball (S : Finset G) (n : ℕ) :
  wordNBall S n ⊆ wordNBall S (n + 1) := by
    rw [wordNBall, wordNBall]
    have h : Finset.range (n + 1) ⊆ Finset.range (n + 1 + 1) := by
      simp only [Finset.range_subset, Nat.le_add_right]
    exact Finset.biUnion_subset_biUnion_of_subset_left (fun x ↦ wordNShell S x) h

lemma wordNBall_monotone (S : Finset G) (m n : ℕ) (hmn : m ≤ n) :
  wordNBall S m ⊆ wordNBall S n := by
    have hmn' : ∃ k : ℕ, n = m + k := Nat.exists_eq_add_of_le hmn
    obtain ⟨ k, hk ⟩ := hmn'
    subst hk
    induction k with
    | zero =>
      rfl
    | succ n ih =>
      have subset_mn1 := wordNBall_subset_wordNPlus1Ball S (m + n)
      simp_all only [Nat.le_add_right, forall_const]
      exact Set.Subset.trans ih subset_mn1

lemma wordNBall_contains_one (S : Finset G) (n : ℕ) :
  (1 : G) ∈ wordNBall S n := by
    have h_one_in_ball_zero : (1 : G) ∈ wordNBall S 0 := by
      simp_all only [wordNBall_zero_eq_one S, Finset.mem_singleton]
    exact wordNBall_monotone S 0 n (Nat.zero_le n) h_one_in_ball_zero

lemma wordNShell_one_eq_S (S : Finset G) :
  wordNShell S 1 = S := by
    rw [wordNShell]
    simp_all [prodOfWord]
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro ⟨w, h⟩
      subst h
      simp_all only [Fin.isValue, Finset.coe_mem]
    · intro hx
      exact ⟨fun _ => ⟨x, hx⟩, rfl⟩

lemma wordNBall_one_eq_S_union_one (S : Finset G) :
  wordNBall S 1 = S ∪ {1} := by
    have h_union := wordNPlus1Ball_union_WordNBall_WordNPlus1Shell S 0
    rw [zero_add] at h_union
    rw [wordNBall_zero_eq_one S, wordNShell_one_eq_S S] at h_union
    rw [Finset.union_comm] at h_union
    exact h_union

lemma shell_subset_ball (S : Finset G) (m n : ℕ) (hmn : m ≤ n) :
  wordNShell S m ⊆ wordNBall S n := by
    rw [wordNBall]
    intro g hg
    simp_all only [Finset.mem_biUnion, Finset.mem_range]
    use m
    simp_all only [and_true]
    exact Nat.lt_add_one_of_le hmn

lemma wordNPlus1Shell_from_wordNShell_left (S : Finset G) (n : ℕ) :
  ∀ w ∈ wordNShell S (n + 1), ∃ s ∈ S, ∃ w' ∈ wordNShell S n,
  w = s * w' := by
    intro w hw
    rw [wordNShell] at hw
    simp only [Finset.mem_image] at hw
    obtain ⟨ f, hf1, hProd ⟩ := hw
    rw [prodOfWord_product_left] at hProd
    use (f 0 : S)
    constructor
    · simp
    · rw [wordNShell]
      simp only [Finset.mem_image]
      use prodOfWord (Fin.tail f)
      have hh : Fin.tail f ∈ Finset.univ := by
        exact Finset.mem_univ (Fin.tail f)
      constructor
      · use (Fin.tail f)
      · subst hProd
        trivial

lemma wordNShell_mul_wordNPlus1Shell_left (S : Finset G) (n : ℕ) :
  ∀ w ∈ wordNShell S n, ∀ s ∈ S, s * w ∈ wordNShell S (n + 1) := by
    intro w h_w s hₛ
    rw [wordNShell]
    rw [wordNShell] at h_w
    rw [Finset.mem_image]
    rw [Finset.mem_image] at h_w
    obtain ⟨ f_n, hf_n, hProd_n ⟩ := h_w
    let s' : S := ⟨ s, hₛ ⟩
    let prod := Matrix.vecCons s' f_n
    use prod
    constructor
    · exact Finset.mem_univ prod
    · have hProd_head : (prod 0 = s) := by
        rfl
      have hProd_tail : prodOfWord (Fin.tail prod) = w := by
        subst hProd_n
        rfl
      rw [prodOfWord_product_left]
      rw [hProd_head, hProd_tail]

lemma wordNShell_mul_wordKShell (S : Finset G) (k n : ℕ) :
  ∀ w ∈ wordNShell S k, ∀ w' ∈ wordNShell S n, w * w' ∈ wordNShell S (k + n) := by
    induction k with
    | zero =>
      intro w hw w' hw'
      simp_all only [zero_add]
      have hw'_one : w = (1 : G) := by
        rw [wordNShell] at hw
        simp only [Finset.univ_unique, Finset.image_singleton, Finset.mem_singleton] at hw
        subst hw
        rfl
      rw [hw'_one, one_mul]
      exact hw'
    | succ k ih =>
      intro w hw w' hw'
      obtain ⟨ s, hsS, wₖ, hwₖ, hw'_eq ⟩ := wordNPlus1Shell_from_wordNShell_left S k w hw
      have h_ih : wₖ * w' ∈ wordNShell S (k + n) := ih wₖ hwₖ w' hw'
      subst hw'_eq
      have move_plus_one : k + 1 + n = (k + n) + 1 := by
        rw [Nat.add_assoc, Nat.add_comm 1 n, ←Nat.add_assoc]
      rw [mul_assoc, move_plus_one]
      exact wordNShell_mul_wordNPlus1Shell_left S (k + n) (wₖ * w') h_ih s hsS

lemma wordNBall_mul_wordKBall (S : Finset G) (k n : ℕ) :
  ∀ w ∈ wordNBall S k, ∀ w' ∈ wordNBall S n, w * w' ∈ wordNBall S (k + n) := by
    intro w hw w' hw'
    rw [wordNBall] at hw hw'
    obtain ⟨ k_w, hk_w, hw_eq ⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨ n_w, hn_w, hw'_eq ⟩ := Finset.mem_biUnion.mp hw'
    simp_all only [Finset.mem_biUnion, Finset.mem_range]
    have h_prod := wordNShell_mul_wordKShell S k_w n_w w hw_eq w' hw'_eq
    have h_lt : k_w + n_w ≤ k + n := by
      apply Nat.le_of_lt_add_one at hn_w
      apply Nat.le_of_lt_add_one at hk_w
      apply Nat.add_le_add hk_w hn_w
    have h_shell_sub_ball := shell_subset_ball S (k_w + n_w) (k + n) h_lt
    exact h_shell_sub_ball h_prod

lemma wordNPlus1Ball_from_wordNBall_left (S : Finset G) (n : ℕ) :
  ∀ w ∈ wordNBall S (n + 1), w = 1 ∨ ∃ s ∈ S, ∃ w' ∈ wordNBall S n,
  w = s * w' := by
    intro w hw
    rw [wordNBall] at hw
    simp only [wordNShell, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_image, Finset.mem_univ, true_and] at hw
    obtain ⟨ m, hm, a, hProd ⟩ := hw
    apply Nat.le_of_lt_add_one at hm
    cases m with
    | zero =>
      left; subst hProd; rfl
    | succ m =>
      right
      use (a 0 : S)
      simp only [Finset.coe_mem, true_and]
      simp only [Nat.add_le_add_iff_right] at hm
      let a' := prodOfWord (Fin.tail a)
      have h_tail_mem : a' ∈ wordNBall S n := by
        have h_tail_mem_shell : a' ∈ wordNShell S m := by
          rw [wordNShell]
          simp only [Finset.mem_image]
          use Fin.tail a
          simp only [Finset.mem_univ, true_and]; rfl
        exact shell_subset_ball S m n hm h_tail_mem_shell
      use a'
      simp only [h_tail_mem, true_and]
      rw [prodOfWord_product_left] at hProd
      subst a'; subst hProd
      rfl

lemma wordKPlusNBall_from_wordNBall (S : Finset G) (k n : ℕ) :
  ∀ w ∈ wordNBall S (k + n), ∃ wₖ ∈ wordNBall S k, ∃ wₙ ∈ wordNBall S n,
  w = wₖ * wₙ := by
    induction k with
    | zero =>
      intro w hw
      rw [zero_add] at hw
      rw [wordNBall_zero_eq_one S]
      use 1
      simp only [Finset.mem_singleton, true_and, one_mul, exists_eq_right']
      exact hw
    | succ k ih =>
      intro w hw
      rw [add_assoc, add_comm 1 n, ←add_assoc] at hw
      obtain h_w_cases := wordNPlus1Ball_from_wordNBall_left S (k + n) w hw
      cases h_w_cases with
      | inl h_eq_one =>
        use 1
        simp_all only [one_mul, exists_eq_right', wordNBall_contains_one S, true_and]
      | inr h_exists =>
        obtain ⟨ s, hsS, w', hw', hw_eq ⟩ := h_exists
        obtain ⟨ wₖ, hwₖ, wₙ, hwₙ, hw'_eq ⟩ := ih w' hw'
        use (s * wₖ)
        constructor
        · have hs_ball : s ∈ wordNBall S 1 := by
            rw [wordNBall_one_eq_S_union_one S]
            simp only [Finset.union_singleton, Finset.mem_insert, hsS, or_true]
          rw [add_comm]
          exact wordNBall_mul_wordKBall S 1 k s hs_ball wₖ hwₖ
        · use wₙ
          constructor
          · exact hwₙ
          · rw [hw_eq, hw'_eq]
            rw [mul_assoc]

lemma wordNBall_closed_under_inv (S : Finset G) (hS : SymmetricFiniteGeneratingSet S) :
  ∀ n : ℕ, ∀ w ∈ wordNBall S n, w⁻¹ ∈ wordNBall S n := by
    intro n
    induction n with
    | zero =>
      intro w hw
      rw [wordNBall_zero_eq_one S] at hw
      simp_all only [Finset.mem_singleton, inv_one, wordNBall_contains_one S 0]
    | succ n ih =>
      intro x hn
      rw [add_comm] at hn
      obtain ⟨ w₁, hw₁, wₙ, hwₙ, hw_eq ⟩ := wordKPlusNBall_from_wordNBall S 1 n x hn
      have h_x_inv_eq : x⁻¹ = wₙ⁻¹ * w₁⁻¹ := by
        rw [hw_eq, mul_inv_rev]
      have h_wn_inv_in_ball : wₙ⁻¹ ∈ wordNBall S n := by
        exact ih wₙ hwₙ
      have h_w1_inv_in_ball : w₁⁻¹ ∈ wordNBall S 1 := by
        rw [wordNBall_one_eq_S_union_one S]
        rw [wordNBall_one_eq_S_union_one S] at hw₁
        rw [Finset.mem_union] at hw₁
        cases hw₁ with
        | inl h_in_S =>
          simp_all only [Finset.union_singleton, Finset.mem_insert, hS.h_inv, or_true]
        | inr h_eq_one =>
          simp_all only [Finset.mem_singleton, Finset.union_singleton, inv_one,
            Finset.mem_insert, true_or]
      have h_inv_prod := wordNBall_mul_wordKBall S n 1 wₙ⁻¹ h_wn_inv_in_ball w₁⁻¹ h_w1_inv_in_ball
      rw [←h_x_inv_eq] at h_inv_prod
      exact h_inv_prod

def allBalls (S : Finset G) : Set G :=
  ⋃ n : ℕ, wordNBall S n

def in_allBalls (S : Finset G) (g : G) (_ : g ∈ Subgroup.closure S) : Prop :=
  g ∈ allBalls S

lemma allBalls_mem (S : Finset G) :
  ∀ (x : G) (hx : x ∈ S), in_allBalls S x (Subgroup.subset_closure hx) := by
    intro x hx
    simp only [in_allBalls, allBalls, Set.mem_iUnion, Finset.mem_coe]
    use 1
    rw [wordNBall]
    simp only [Finset.mem_biUnion]
    use 1
    constructor
    · simp
    · rw [wordNShell]
      simp only [Finset.mem_image, Finset.mem_univ]
      simp
      use fun i ↦ ⟨ x, hx ⟩
      rw [prodOfWord]
      simp

lemma allBalls_one (S : Finset G) :
  in_allBalls S (1 : G) (Subgroup.one_mem ((Subgroup.closure S) : Subgroup G)) := by
    simp only [in_allBalls, allBalls, Set.mem_iUnion, Finset.mem_coe]
    use 0
    rw [wordNBall]
    simp only [Finset.mem_biUnion]
    use 0
    simp only [zero_add, Finset.range_one, Finset.mem_singleton, true_and]
    rw [wordNShell]
    simp only [Finset.mem_image, Finset.mem_univ, Fin.exists_fin_zero_pi, true_and]
    rfl

lemma allBalls_mul (S : Finset G) :
  ∀ (x y : G)
    (hx : x ∈ (Subgroup.closure S : Subgroup G))
    (hy : y ∈ (Subgroup.closure S : Subgroup G)),
    (in_allBalls S x hx) → (in_allBalls S y hy) → (in_allBalls S (x * y) (Subgroup.mul_mem ((Subgroup.closure S) : Subgroup G) hx hy)) := by
    intro x y _hx _hy hx hy
    rw [in_allBalls, allBalls, Set.mem_iUnion] at hx hy ⊢
    obtain ⟨ n_x, hn_x ⟩ := hx
    obtain ⟨ n_y, hn_y ⟩ := hy
    let n := n_x + n_y
    use n
    have h_le : n_x + n_y ≤ n := by
      rfl
    apply wordNBall_monotone S (n_x + n_y) n h_le
    exact wordNBall_mul_wordKBall S n_x n_y x hn_x y hn_y

lemma allBalls_inv (S : Finset G) (hS : SymmetricFiniteGeneratingSet S) :
  ∀ (x : G) (hx : x ∈ (Subgroup.closure (S : Finset G) : Subgroup G)),
    (in_allBalls S x hx) → (in_allBalls S x⁻¹ (Subgroup.inv_mem (Subgroup.closure (S : Finset G) : Subgroup G) hx)) := by
    intro x hx_closure hx_allBalls
    rw [in_allBalls, allBalls, Set.mem_iUnion] at hx_allBalls ⊢
    obtain ⟨ n, hn ⟩ := hx_allBalls
    exact ⟨n, wordNBall_closed_under_inv S hS n x hn⟩

lemma wordNBalls_cover_G {S : Finset G} (hS : SymmetricFiniteGeneratingSet S) :
  allBalls S = (⊤ : Subgroup G).carrier := by
    ext g
    constructor
    · simp
    · intro hg
      have h_inv := hS.h_inv
      have h_gen := hS.h_gen
      rw [FiniteGeneratingSet] at h_gen
      have h_union_closure : (Subgroup.closure (S : Set G)).carrier ⊆ allBalls S := by
        intro g' hg'
        let p := in_allBalls S
        exact @Subgroup.closure_induction G _ S p (allBalls_mem S) (allBalls_one S) (allBalls_mul S) (allBalls_inv S hS) g' hg'
      rw [←h_gen] at hg
      apply Set.mem_of_subset_of_mem h_union_closure hg

lemma mem_allBalls {S : Finset G} (hS : SymmetricFiniteGeneratingSet S) (g : G) :
  g ∈ allBalls S := by
    rw [wordNBalls_cover_G hS]
    simp only [Subgroup.top_toSubmonoid, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
      Submonoid.mem_top]

lemma finset_in_CBall (S S' : Finset G) (hS : SymmetricFiniteGeneratingSet S') :
  ∃ C : ℕ, S ⊆ wordNBall S' C := by
    have h_s_in_ball : ∀ s ∈ S, ∃ C_s : ℕ, s ∈ wordNBall S' C_s := by
      intro s hs
      have h_s_in_allBalls := mem_allBalls hS s
      rw [allBalls, Set.mem_iUnion] at h_s_in_allBalls
      simp_all only [Finset.mem_coe]
    let f_C : S → ℕ := fun ⟨s, hs⟩ ↦ Nat.find (h_s_in_ball s hs)
    let C := Finset.univ.sup f_C
    have h_C_bound : ∀ s : S, f_C s ≤ C := by
      intro s
      apply Finset.le_sup
      simp only [Finset.mem_univ]
    have h_C_member : ∀ s ∈ S, s ∈ wordNBall S' C := by
      intro s hs
      apply wordNBall_monotone S' (f_C ⟨s, hs⟩) C (h_C_bound ⟨s, hs⟩)
      exact Nat.find_spec (h_s_in_ball s hs)
    use C
    intro s hs
    exact h_C_member s hs

lemma wordNBall_subset_equiv (S S' : Finset G) (hS' : SymmetricFiniteGeneratingSet S') :
  ∃ C : ℕ, ∀ n : ℕ, wordNBall S n ⊆ wordNBall S' (C * n) := by
    obtain ⟨ C, hC ⟩ := finset_in_CBall S S' hS'
    use C
    intro n
    induction n with
    | zero =>
      simp only [Nat.mul_zero, wordNBall_zero_eq_one, Finset.singleton_subset_iff]
      exact wordNBall_contains_one S' 0
    | succ n ih =>
      intro g hg
      obtain h_cases := wordNPlus1Ball_from_wordNBall_left S n g hg
      cases h_cases with
      | inl h_eq_one =>
        subst h_eq_one
        exact wordNBall_contains_one S' (C * (n + 1))
      | inr h_exists =>
        obtain ⟨s, hsS, w', hw', hw_eq⟩ := h_exists
        have h_s_in_C : s ∈ wordNBall S' C := hC hsS
        have h_w'_in_Cn : w' ∈ wordNBall S' (C * n) := ih hw'
        have h_prod_in_C_plus_Cn := wordNBall_mul_wordKBall S' C (C * n) s h_s_in_C w' h_w'_in_Cn
        have move_plus_one : C * (n + 1) = C + C * n := by
          rw [Nat.mul_succ, Nat.add_comm]
        rw [move_plus_one]
        subst hw_eq; exact h_prod_in_C_plus_Cn

lemma wordNBall_subset_equiv' (S S' : Finset G) (hS' : SymmetricFiniteGeneratingSet S') :
  ∃ C : ℕ, C > 0 ∧ ∀ n : ℕ, wordNBall S n ⊆ wordNBall S' (C * n) := by
    obtain ⟨ C, hC ⟩ := wordNBall_subset_equiv S S' hS'
    use C + 1
    constructor
    · exact Nat.succ_pos C
    · intro n
      have h_mul : C * n ≤ (C + 1) * n := by
        rw [Nat.add_one_mul]
        exact Nat.le_add_right (C * n) n
      specialize hC n
      have h_sub : wordNBall S' (C * n) ⊆ wordNBall S' ((C + 1) * n) := wordNBall_monotone S' (C * n) ((C + 1) * n) h_mul
      exact Finset.Subset.trans hC h_sub

noncomputable
def growthRate (S : Finset G) (n : ℕ) : ℕ :=
  (wordNBall S n).card

def GrowthEquiv (f g : ℕ → ℕ) : Prop :=
  ∃ C₁ C₂ : ℕ, C₁ > 0 ∧ C₂ > 0 ∧ ∀ᶠ n in Filter.atTop, f n ≤ g (C₁ * n) ∧ g n ≤ f (C₂ * n)

def GrowsLike (G : Type) [Group G] (f : ℕ → ℕ) : Prop :=
  ∃ (S : Finset G), SymmetricFiniteGeneratingSet S ∧ GrowthEquiv (growthRate S) f

theorem growthRatesEquiv (f g : ℕ → ℕ) : GrowsLike G f → GrowsLike G g → GrowthEquiv f g := by
    intro h_f h_g

    obtain ⟨ S_f, hS_f, h_equiv_f ⟩ := h_f
    rw [GrowthEquiv] at h_equiv_f
    unfold growthRate at h_equiv_f

    obtain ⟨ S_g, hS_g, h_equiv_g ⟩ := h_g
    rw [GrowthEquiv] at h_equiv_g
    unfold growthRate at h_equiv_g

    obtain ⟨ C_f1, C_f2, hC_f1, hC_f2, hC_f ⟩ := h_equiv_f
    obtain ⟨ C_g1, C_g2, hC_g1, hC_g2, hC_g ⟩ := h_equiv_g

    apply Filter.eventually_atTop.mp at hC_f
    apply Filter.eventually_atTop.mp at hC_g

    obtain ⟨ a_f, h_ab_f ⟩ := hC_f
    obtain ⟨ a_g, h_ab_g ⟩ := hC_g

    rw [forall₂_and] at h_ab_f h_ab_g

    have h_f_lbound := h_ab_f.1
    have h_f_ubound := h_ab_f.2
    have h_g_lbound := h_ab_g.1
    have h_g_ubound := h_ab_g.2

    obtain ⟨ C₁, hC₁ ⟩ := wordNBall_subset_equiv' S_f S_g hS_g
    obtain ⟨ C₂, hC₂ ⟩ := wordNBall_subset_equiv' S_g S_f hS_f

    have hC₁_pos : C₁ > 0 := hC₁.1
    have hC₁_bound := hC₁.2
    have hC₂_pos : C₂ > 0 := hC₂.1
    have hC₂_bound := hC₂.2

    let E₁ := C_g1 * C₁ * C_f2; let E₂ := C_f1 * C₂ * C_g2
    use E₁, E₂

    have hE₁_pos : E₁ > 0 := by
      simp_all only [gt_iff_lt, ge_iff_le, implies_true, and_self, Nat.mul_pos_iff_of_pos_left, E₁]
    have hE₂_pos : E₂ > 0 := by
      simp_all only [gt_iff_lt, ge_iff_le, implies_true, and_self, Nat.mul_pos_iff_of_pos_left, E₂]

    apply And.intro hE₁_pos; apply And.intro hE₂_pos

    apply Filter.eventually_atTop.mpr

    use a_f + a_g
    intro n hn

    have h_nbound_f : n ≥ a_f := by
      exact Nat.le_of_add_right_le hn
    have h_nbound_g : n ≥ a_g := by
      exact Nat.le_of_add_left_le hn

    constructor
    · have h_f1 : f n ≤ (wordNBall S_f (C_f2 * n)).card := by
        apply h_f_ubound n h_nbound_f
      have h_f2 : (wordNBall S_f (C_f2 * n)).card ≤ (wordNBall S_g (C₁ * C_f2 * n)).card := by
        apply Finset.card_le_card
        rw [mul_assoc]
        exact hC₁_bound (C_f2 * n)
      have h_f3 : (wordNBall S_g (C₁ * C_f2 * n)).card ≤ g ((C_g1 * C₁ * C_f2) * n) := by
        have h_prod : (C_g1 * (C₁ * C_f2 * n)) = (C_g1 * C₁ * C_f2 * n) := by
          rw [mul_assoc, mul_assoc, mul_assoc]
        rw [←h_prod]
        apply h_g_lbound (C₁ * C_f2 * n)
        have h_mul : C₁ * C_f2 ≥ 1 := by
          exact Right.one_le_mul hC₁_pos hC_f2
        have h_mul_n : C₁ * C_f2 * n ≥ n := by
          exact Nat.le_mul_of_pos_left n h_mul
        exact Nat.le_trans h_nbound_g h_mul_n
      calc f n
        _ ≤ (wordNBall S_f (C_f2 * n)).card := h_f1
        _ ≤ (wordNBall S_g (C₁ * C_f2 * n)).card := h_f2
        _ ≤ g ((C_g1 * C₁ * C_f2) * n) := h_f3
    · have h_g1 : g n ≤ (wordNBall S_g (C_g2 * n)).card := by
        apply h_g_ubound n h_nbound_g
      have h_g2 : (wordNBall S_g (C_g2 * n)).card ≤ (wordNBall S_f (C₂ * C_g2 * n)).card := by
        apply Finset.card_le_card
        rw [mul_assoc]
        exact hC₂_bound (C_g2 * n)
      have h_g3 : (wordNBall S_f (C₂ * C_g2 * n)).card ≤ f ((C_f1 * C₂ * C_g2) * n) := by
        have h_prod : (C_f1 * (C₂ * C_g2 * n)) = (C_f1 * C₂ * C_g2 * n) := by
          rw [mul_assoc, mul_assoc, mul_assoc]
        rw [←h_prod]
        apply h_f_lbound (C₂ * C_g2 * n)
        have h_mul : C₂ * C_g2 ≥ 1 := by
          exact Right.one_le_mul hC₂_pos hC_g2
        have h_mul_n : C₂ * C_g2 * n ≥ n := by
          exact Nat.le_mul_of_pos_left n h_mul
        exact Nat.le_trans h_nbound_f h_mul_n
      calc g n
        _ ≤ (wordNBall S_g (C_g2 * n)).card := h_g1
        _ ≤ (wordNBall S_f (C₂ * C_g2 * n)).card := h_g2
        _ ≤ f ((C_f1 * C₂ * C_g2) * n) := h_g3

/--
Other stuff I proved but didn't use above
-/

lemma wordNShell_subset_H (S : Finset G) (H : Subgroup G) (hS : (S : Set G) ⊆ H.carrier) :
  ∀ n : ℕ, (wordNShell S n : Set G) ⊆ H.carrier := by
    intro n
    induction n with
    | zero =>
      simp [wordNShell, prodOfWord]
    | succ n ih =>
      intro g hg
      rw [wordNShell] at hg
      obtain ⟨ s, hsS, w', hw', hw_eq ⟩ := wordNPlus1Shell_from_wordNShell_left S n g hg
      have hw'_H : w' ∈ H.carrier := ih hw'
      subst hw_eq
      simp_all only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid,
        Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      obtain ⟨w, h⟩ := hg
      apply MulMemClass.mul_mem
      · apply hS
        exact hsS
      · exact hw'_H

lemma wordNBall_subset_H (S : Finset G) (H : Subgroup G) (hS : (S : Set G) ⊆ H.carrier) :
  ∀ n : ℕ, (wordNBall S n : Set G) ⊆ H.carrier := by
    intro n
    rw [wordNBall]
    intro g hg
    obtain ⟨ k, hk, hg_eq ⟩ := Finset.mem_biUnion.mp hg
    have hNShell_H : (wordNShell S k : Set G) ⊆ H.carrier := wordNShell_subset_H S H hS k
    exact hNShell_H hg_eq

lemma wordKPlusNShell_from_wordNShell (S : Finset G) (k n : ℕ) :
  ∀ w ∈ wordNShell S (k + n), ∃ wₖ ∈ wordNShell S k, ∃ wₙ ∈ wordNShell S n,
  w = wₖ * wₙ := by
    induction k with
    | zero =>
      intro w hw
      use 1
      constructor
      · simp [wordNShell, prodOfWord]
      · use w
        constructor
        · rw [zero_add] at hw
          exact hw
        · simp
    | succ k ih =>
      intro w hw
      rw [add_assoc, add_comm 1 n, ←add_assoc] at hw
      obtain ⟨ s, hsS, w', hw', hw_eq ⟩ := wordNPlus1Shell_from_wordNShell_left S (k + n) w hw
      obtain ⟨ wₖ, hwₖ, wₙ, hwₙ, hw'_eq ⟩ := ih w' hw'
      use (s * wₖ)
      constructor
      · simp [wordNShell_mul_wordNPlus1Shell_left S k wₖ hwₖ s hsS]
      · use wₙ
        constructor
        · exact hwₙ
        · rw [hw_eq, hw'_eq]
          rw [mul_assoc]

lemma wordNPlus1Shell_from_wordNShell_right (S : Finset G) (n : ℕ) :
  ∀ w ∈ wordNShell S (n + 1), ∃ s ∈ S, ∃ w' ∈ wordNShell S n,
  w = w' * s := by
    let h_kPlusN := wordKPlusNShell_from_wordNShell S n 1
    rw [wordNShell_one_eq_S S] at h_kPlusN
    intro w hw
    obtain ⟨ wₙ, hwₙ, s, hsS, hw_eq ⟩ := h_kPlusN w hw
    use s
    constructor
    · exact hsS
    · use wₙ

lemma wordNPlusKShell_from_wordNShell (S : Finset G) (k n : ℕ) :
  ∀ w ∈ wordNShell S (k + n), ∃ wₖ ∈ wordNShell S k, ∃ wₙ ∈ wordNShell S n,
  w = wₖ * wₙ := by
    induction k with
    | zero =>
      intro w hw
      use 1
      constructor
      · simp [wordNShell, prodOfWord]
      · use w
        constructor
        · simp_all
        · simp
    | succ k ih =>
      intro w hw
      rw [add_assoc, add_comm 1 n, ←add_assoc] at hw
      obtain ⟨ s, hsS, w', hw', hw_eq ⟩ := wordNPlus1Shell_from_wordNShell_left S (k + n) w hw
      obtain ⟨ wₖ, hwₖ, wₙ, hwₙ, hw'_eq ⟩ := ih w' hw'
      use (s * wₖ)
      constructor
      · simp [wordNShell_mul_wordNPlus1Shell_left S k wₖ hwₖ s hsS]
      · use wₙ
        constructor
        · exact hwₙ
        · rw [hw_eq, hw'_eq]
          rw [mul_assoc]

lemma wordNShell_card_bound (S : Finset G) (n : ℕ) :
  (wordNShell S n).card ≤ (S.card) ^ n := by
    rw [wordNShell]
    let h_words : Finset (Fin n → S) := Finset.univ
    have h_image_card : (h_words.image (fun w ↦ prodOfWord w)).card ≤ h_words.card := by
      apply Finset.card_image_le
    have h_words_card : h_words.card = (S.card) ^ n := by
      rw [Finset.card_univ, Fintype.card_pi, Fintype.card_coe, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    subst h_words
    rw [h_words_card] at h_image_card
    exact h_image_card

lemma wordNShell_card_bound_prod (S : Finset G) (n m : ℕ) :
  (wordNShell S (n + m)).card ≤ (S.card) ^ n * (wordNShell S m).card := by
    have h_surj : wordNShell S (n + m) ⊆
        (wordNShell S n ×ˢ wordNShell S m).image (fun ⟨wₙ, wₘ⟩ ↦ wₙ * wₘ) := by
      intro w hw
      obtain ⟨wₙ, hwₙ, wₘ, hwₘ, hw_eq⟩ := wordNPlusKShell_from_wordNShell S n m w hw
      simp only [Finset.mem_image, Finset.mem_product]
      use (wₙ, wₘ)
      subst hw_eq
      simp_all only [and_self]
    have h_subset_card : (wordNShell S (n + m)).card ≤
        ((wordNShell S n ×ˢ wordNShell S m).image (fun ⟨wₙ, wₘ⟩ ↦ wₙ * wₘ)).card := by
      apply Finset.card_le_card
      exact h_surj
    have h_image_card : ((wordNShell S n ×ˢ wordNShell S m).image (fun ⟨wₙ, wₘ⟩ ↦ wₙ * wₘ)).card
        ≤ (wordNShell S n ×ˢ wordNShell S m).card := Finset.card_image_le
    have h_product_card : (wordNShell S n ×ˢ wordNShell S m).card =
        (wordNShell S n).card * (wordNShell S m).card := by apply Finset.card_product
    have h_shell_bound_prod : (wordNShell S n).card * (wordNShell S m).card
        ≤ S.card ^ n * (wordNShell S m).card := by
      have h_shell_bound := wordNShell_card_bound S n
      exact Nat.mul_le_mul_right (wordNShell S m).card h_shell_bound
    calc (wordNShell S (n + m)).card
       _ ≤ ((wordNShell S n ×ˢ wordNShell S m).image (fun ⟨wₙ, wₘ⟩ ↦ wₙ * wₘ)).card := h_subset_card
       _ ≤ (wordNShell S n ×ˢ wordNShell S m).card := h_image_card
       _ = (wordNShell S n).card * (wordNShell S m).card := h_product_card
       _ ≤ S.card ^ n * (wordNShell S m).card := h_shell_bound_prod
