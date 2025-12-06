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
import Mathlib.GroupTheory.Finiteness
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Basic


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
    · intro s a
      simp_all only [S', S_inv, Finset.mem_union, Finset.mem_image]
      cases a with
      | inl hsS => right; simp only [inv_inj]; use s
      | inr hsS_inv =>
        left
        obtain ⟨ s', hs'S, hs_eq ⟩ := hsS_inv
        subst hs_eq; simp_all only [inv_inv]
    · have hSub : S ⊆ S' := Finset.subset_union_left
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

lemma wordBall_zero_eq_one (S : Finset G) :
  wordBall S 0 = {1} := by
    rfl

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
      have ha_one : a = (1 : G) := by
        rw [wordShell_zero_eq_one S] at ha
        simp only [Finset.mem_singleton] at ha; exact ha
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
    | zero =>
      left
      rw [wordShell_zero_eq_one S] at ha
      exact Finset.mem_singleton.mp ha
    | succ m' =>
      right
      obtain ⟨ s, hsS, a', ha', ha_eq ⟩ := wordShell_element_is_product_left S m' a ha
      use s, hsS, a', shell_subset_ball S (Nat.le_of_lt_succ hm) ha'

lemma wordBall_element_is_product (S : Finset G) (k n : ℕ) :
  ∀ a ∈ wordBall S (k + n), ∃ aₖ ∈ wordBall S k, ∃ aₙ ∈ wordBall S n,
  a = aₖ * aₙ := by
    induction k with
    | zero =>
      intro a ha
      rw [wordBall_zero_eq_one S]; rw [zero_add] at ha
      use 1, Finset.mem_singleton.mpr rfl, a, ha
      rw [one_mul]
    | succ k ih =>
      intro a ha
      rw [add_assoc, add_comm 1 n, ←add_assoc] at ha
      obtain h_a_cases := wordBall_element_is_product_left S (k + n) a ha
      cases h_a_cases with
      | inl h_eq_one =>
        use 1, wordBall_contains_one S (k + 1), 1, wordBall_contains_one S n
        rw [h_eq_one, one_mul]
      | inr h_prod =>
        obtain ⟨ s, hsS, a', ha', ha_prod ⟩ := h_prod
        obtain ⟨ aₖ, haₖ, aₙ, haₙ, ha'_prod ⟩ := ih a' ha'
        use (s * aₖ)
        constructor
        · exact element_wordBall_product_in_wordBall S k s hsS aₖ haₖ
        · use aₙ, haₙ
          rw [ha_prod, ha'_prod, mul_assoc]

-- TODO: Continue tidying from here
lemma wordBall_closed_under_inv (S : Finset G) (hS : SymmetricFiniteGeneratingSet S) :
  ∀ n : ℕ, ∀ w ∈ wordBall S n, w⁻¹ ∈ wordBall S n := by
    intro n
    induction n with
    | zero =>
      intro w hw
      rw [wordBall_zero_eq_one S] at hw ⊢
      simp_all only [Finset.mem_singleton, inv_one]
    | succ n ih =>
      intro x hn
      rw [add_comm] at hn
      obtain ⟨ w₁, hw₁, wₙ, hwₙ, hw_eq ⟩ := wordBall_element_is_product S 1 n x hn
      have h_x_inv_eq : x⁻¹ = wₙ⁻¹ * w₁⁻¹ := by
        rw [hw_eq, mul_inv_rev]
      have h_wn_inv_in_ball : wₙ⁻¹ ∈ wordBall S n := by
        exact ih wₙ hwₙ
      have h_w1_inv_in_ball : w₁⁻¹ ∈ wordBall S 1 := by
        rw [wordBall_one_eq_S_union_one S]
        rw [wordBall_one_eq_S_union_one S] at hw₁
        rw [Finset.mem_union] at hw₁
        cases hw₁ with
        | inl h_in_S =>
          simp_all only [Finset.union_singleton, Finset.mem_insert, hS.h_inv, or_true]
        | inr h_eq_one =>
          simp_all only [Finset.mem_singleton, Finset.union_singleton, inv_one,
            Finset.mem_insert, true_or]
      have h_inv_prod := wordBall_mul_wordBall S n 1 wₙ⁻¹ h_wn_inv_in_ball w₁⁻¹ h_w1_inv_in_ball
      rw [←h_x_inv_eq] at h_inv_prod
      exact h_inv_prod

def allBalls (S : Finset G) : Set G :=
  ⋃ n : ℕ, wordBall S n

def in_allBalls (S : Finset G) (g : G) (_ : g ∈ Subgroup.closure S) : Prop :=
  g ∈ allBalls S

lemma allBalls_mem (S : Finset G) :
  ∀ (x : G) (hx : x ∈ S), in_allBalls S x (Subgroup.subset_closure hx) := by
    intro x hx
    simp only [in_allBalls, allBalls, Set.mem_iUnion, Finset.mem_coe]
    use 1
    rw [wordBall]
    simp only [Finset.mem_biUnion]
    use 1
    constructor
    · simp
    · rw [wordShell]
      simp only [Finset.mem_image, Finset.mem_univ]
      simp
      use fun i ↦ ⟨ x, hx ⟩
      rw [prodOfWord]
      simp

lemma allBalls_one (S : Finset G) :
  in_allBalls S (1 : G) (Subgroup.one_mem ((Subgroup.closure S) : Subgroup G)) := by
    simp only [in_allBalls, allBalls, Set.mem_iUnion, Finset.mem_coe]
    use 0
    rw [wordBall]
    simp only [Finset.mem_biUnion]
    use 0
    simp only [zero_add, Finset.range_one, Finset.mem_singleton, true_and]
    rw [wordShell]
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
    apply wordBall_monotone S h_le
    exact wordBall_mul_wordBall S n_x n_y x hn_x y hn_y

lemma allBalls_inv (S : Finset G) (hS : SymmetricFiniteGeneratingSet S) :
  ∀ (x : G) (hx : x ∈ (Subgroup.closure (S : Finset G) : Subgroup G)),
    (in_allBalls S x hx) → (in_allBalls S x⁻¹ (Subgroup.inv_mem (Subgroup.closure (S : Finset G) : Subgroup G) hx)) := by
    intro x hx_closure hx_allBalls
    rw [in_allBalls, allBalls, Set.mem_iUnion] at hx_allBalls ⊢
    obtain ⟨ n, hn ⟩ := hx_allBalls
    exact ⟨n, wordBall_closed_under_inv S hS n x hn⟩

lemma allBalls_cover_G {S : Finset G} (hS : SymmetricFiniteGeneratingSet S) :
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
    rw [allBalls_cover_G hS]
    simp only [Subgroup.top_toSubmonoid, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
      Submonoid.mem_top]

lemma finset_in_wordBall (S S' : Finset G) (hS : SymmetricFiniteGeneratingSet S') :
  ∃ C : ℕ, S ⊆ wordBall S' C := by
    have h_s_in_ball : ∀ s ∈ S, ∃ C_s : ℕ, s ∈ wordBall S' C_s := by
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
    have h_C_element : ∀ s ∈ S, s ∈ wordBall S' C := by
      intro s hs
      apply wordBall_monotone S' (h_C_bound ⟨s, hs⟩)
      exact Nat.find_spec (h_s_in_ball s hs)
    use C
    intro s hs
    exact h_C_element s hs

lemma wordBall_S_subset_wordBall_S' (S S' : Finset G) (hS' : SymmetricFiniteGeneratingSet S') :
  ∃ C : ℕ, ∀ n : ℕ, wordBall S n ⊆ wordBall S' (C * n) := by
    obtain ⟨ C, hC ⟩ := finset_in_wordBall S S' hS'
    use C
    intro n
    induction n with
    | zero =>
      simp only [Nat.mul_zero, wordBall_zero_eq_one, Finset.singleton_subset_iff]
      exact wordBall_contains_one S' 0
    | succ n ih =>
      intro g hg
      obtain h_cases := wordBall_element_is_product_left S n g hg
      cases h_cases with
      | inl h_eq_one =>
        subst h_eq_one
        exact wordBall_contains_one S' (C * (n + 1))
      | inr h_exists =>
        obtain ⟨s, hsS, w', hw', hw_eq⟩ := h_exists
        have h_s_in_C : s ∈ wordBall S' C := hC hsS
        have h_w'_in_Cn : w' ∈ wordBall S' (C * n) := ih hw'
        have h_prod_in_C_plus_Cn := wordBall_mul_wordBall S' C (C * n) s h_s_in_C w' h_w'_in_Cn
        have move_plus_one : C * (n + 1) = C + C * n := by
          rw [Nat.mul_succ, Nat.add_comm]
        rw [move_plus_one]
        subst hw_eq; exact h_prod_in_C_plus_Cn

lemma wordBall_S_subset_wordBall_S'_succ (S S' : Finset G) (hS' : SymmetricFiniteGeneratingSet S') :
  ∃ C : ℕ, C > 0 ∧ ∀ n : ℕ, wordBall S n ⊆ wordBall S' (C * n) := by
    obtain ⟨ C, hC ⟩ := wordBall_S_subset_wordBall_S' S S' hS'
    use C + 1
    constructor
    · exact Nat.succ_pos C
    · intro n
      have h_mul : C * n ≤ (C + 1) * n := by
        rw [Nat.add_one_mul]
        exact Nat.le_add_right (C * n) n
      specialize hC n
      have h_sub : wordBall S' (C * n) ⊆ wordBall S' ((C + 1) * n) := wordBall_monotone S' h_mul
      exact Finset.Subset.trans hC h_sub

noncomputable
def growthRate (S : Finset G) (n : ℕ) : ℕ :=
  (wordBall S n).card

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

    obtain ⟨ C₁, hC₁ ⟩ := wordBall_S_subset_wordBall_S'_succ S_f S_g hS_g
    obtain ⟨ C₂, hC₂ ⟩ := wordBall_S_subset_wordBall_S'_succ S_g S_f hS_f

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
    · have h_f1 : f n ≤ (wordBall S_f (C_f2 * n)).card := by
        apply h_f_ubound n h_nbound_f
      have h_f2 : (wordBall S_f (C_f2 * n)).card ≤ (wordBall S_g (C₁ * C_f2 * n)).card := by
        apply Finset.card_le_card
        rw [mul_assoc]
        exact hC₁_bound (C_f2 * n)
      have h_f3 : (wordBall S_g (C₁ * C_f2 * n)).card ≤ g ((C_g1 * C₁ * C_f2) * n) := by
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
        _ ≤ (wordBall S_f (C_f2 * n)).card := h_f1
        _ ≤ (wordBall S_g (C₁ * C_f2 * n)).card := h_f2
        _ ≤ g ((C_g1 * C₁ * C_f2) * n) := h_f3
    · have h_g1 : g n ≤ (wordBall S_g (C_g2 * n)).card := by
        apply h_g_ubound n h_nbound_g
      have h_g2 : (wordBall S_g (C_g2 * n)).card ≤ (wordBall S_f (C₂ * C_g2 * n)).card := by
        apply Finset.card_le_card
        rw [mul_assoc]
        exact hC₂_bound (C_g2 * n)
      have h_g3 : (wordBall S_f (C₂ * C_g2 * n)).card ≤ f ((C_f1 * C₂ * C_g2) * n) := by
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
        _ ≤ (wordBall S_g (C_g2 * n)).card := h_g1
        _ ≤ (wordBall S_f (C₂ * C_g2 * n)).card := h_g2
        _ ≤ f ((C_f1 * C₂ * C_g2) * n) := h_g3

/--
Other stuff I proved but didn't use above
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

lemma wordShell_element_is_product (S : Finset G) (k n : ℕ) :
  ∀ w ∈ wordShell S (k + n), ∃ wₖ ∈ wordShell S k, ∃ wₙ ∈ wordShell S n,
  w = wₖ * wₙ := by
    induction k with
    | zero =>
      intro w hw
      use 1
      constructor
      · simp [wordShell, prodOfWord]
      · use w
        constructor
        · rw [zero_add] at hw
          exact hw
        · simp
    | succ k ih =>
      intro w hw
      rw [add_assoc, add_comm 1 n, ←add_assoc] at hw
      obtain ⟨ s, hsS, w', hw', hw_eq ⟩ := wordShell_element_is_product_left S (k + n) w hw
      obtain ⟨ wₖ, hwₖ, wₙ, hwₙ, hw'_eq ⟩ := ih w' hw'
      use (s * wₖ)
      constructor
      · simp [wordShell_mul_element_left S k wₖ hwₖ s hsS]
      · use wₙ
        constructor
        · exact hwₙ
        · rw [hw_eq, hw'_eq]
          rw [mul_assoc]

lemma wordShell_element_is_product_rightight (S : Finset G) (n : ℕ) :
  ∀ w ∈ wordShell S (n + 1), ∃ s ∈ S, ∃ w' ∈ wordShell S n,
  w = w' * s := by
    let h_kPlusN := wordShell_element_is_product S n 1
    rw [wordShell_one_eq_S S] at h_kPlusN
    intro w hw
    obtain ⟨ wₙ, hwₙ, s, hsS, hw_eq ⟩ := h_kPlusN w hw
    use s
    constructor
    · exact hsS
    · use wₙ

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
      obtain ⟨wₙ, hwₙ, wₘ, hwₘ, hw_eq⟩ := wordShell_element_is_product S n m w hw
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
