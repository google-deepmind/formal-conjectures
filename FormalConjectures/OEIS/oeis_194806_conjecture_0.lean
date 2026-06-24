/-
Copyright 2026 Google LLC

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

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option maxHeartbeats 200000




open Finset Nat

/-- The set of all products of elements from a Finset S. -/
def set_prod (S : Finset ℕ) : Finset ℕ :=
  (S.product S).image fun p : ℕ × ℕ => p.fst * p.snd

/--
A194806: Size of the smallest subset $S$ of $T = \{1,2,3,\dots,n\}$ such that $S \cdot S$ contains $T$,
where $S \cdot S$ is the set of all products of elements of $S$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let T_n := Icc 1 n

    -- The set of subsets $S \subseteq T_n$ such that $T_n \subseteq S \cdot S$.
    let valid_subsets : Finset (Finset ℕ) :=
      T_n.powerset.filter (fun S : Finset ℕ => T_n ⊆ set_prod S)

    -- Proof that $T_n$ is guaranteed to be a valid subset, ensuring `valid_subsets` is non-empty.
    have T_n_is_valid : T_n ∈ valid_subsets := by
      apply mem_filter.mpr
      constructor
      -- 1. T_n ∈ T_n.powerset (i.e., T_n ⊆ T_n)
      apply mem_powerset.mpr; rfl
      -- 2. T_n ⊆ set_prod T_n
      intro k hk

      have one_le_n : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)
      have h1 : 1 ∈ T_n := mem_Icc.mpr ⟨Nat.le_refl 1, one_le_n⟩

      -- We show k = k * 1 is in set_prod T_n
      -- set_prod T_n is the image of T_n × T_n under multiplication.
      simp only [set_prod, mem_image, Prod.exists]
      use k, 1
      constructor
      -- Show that (k, 1) ∈ T_n × T_n
      · exact mem_product.mpr ⟨hk, h1⟩
      -- Show that k * 1 = k
      · exact Nat.mul_one k

    have h_nonempty : valid_subsets.Nonempty := ⟨T_n, T_n_is_valid⟩

    let sizes := valid_subsets.image Finset.card

    -- The min' function requires proof that the finset is non-empty.
    have h_sizes_nonempty : sizes.Nonempty := h_nonempty.image Finset.card

    -- We return the minimum card of all valid subsets.
    sizes.min' h_sizes_nonempty

open MeasureTheory

open Polynomial

open scoped BigOperators

open scoped Classical

open scoped ENNReal

open scoped EuclideanGeometry

open scoped InnerProductSpace

open scoped intervalIntegral

open scoped List

open scoped Matrix

open scoped Nat

open scoped NNReal

open scoped Pointwise

open scoped ProbabilityTheory

open scoped Real

open scoped symmDiff

open scoped Topology

-- EVOLVE-BLOCK-START
lemma choose_lower_bound (m : ℕ) : 2^m ≤ Nat.choose (2 * m) m := by
  exact (m.rec (by decide) (fun A B=>pow_succ (2) A▸ (2 * A+1).choose_succ_succ A▸ (2 * A).choose_succ_succ A▸by linarith [ (2 * A).choose_le_succ A]))

lemma choose_upper_bound (m : ℕ) :
    Nat.choose (2 * m) m ≤ (2 * m) ^ (Nat.primeCounting (2 * m)) := by
  use if a:m=0 then (a▸refl _)else(Nat.factorization_prod_pow_eq_self<|Nat.choose_ne_zero (by valid)).ge.trans (.trans (?_) (by rw [Nat.primeCounting]))
  rewrite[Nat.primeCounting', Finsupp.prod_of_support_subset (s := { a ∈.range (2 *m+1)|a.Prime})]
  · exact (Nat.count_eq_card_filter_range Nat.Prime _)▸ Finset.prod_le_pow_card _ _ _ fun and x =>Nat.pow_factorization_choose_le (by positivity)
  · refine fun and=>by simp_all[ two_mul,Nat.Prime.dvd_factorial ↑_|>.mp.comp (.trans ↑_) (Nat.choose_eq_factorial_div_factorial ↑le_self_add▸Nat.div_dvd_of_dvd ↑(Nat.factorial_mul_factorial_dvd_factorial _)), and.lt_succ_iff]
  · subsingleton

lemma two_pow_le_pow_primeCounting (m : ℕ) :
    2^m ≤ (2 * m) ^ (Nat.primeCounting (2 * m)) := by
  exact le_trans (choose_lower_bound m) (choose_upper_bound m)

lemma n_le_two_pow_cbrt (x : ℕ) (hx : 10 ≤ x) : x^3 ≤ 2^x := by
  refine(10).le_induction (by decide) ( fun and K V' =>pow_succ (2) and▸by nlinarith only [ K,pow_three and▸V']) ↑x hx

noncomputable def K (n : ℕ) : ℕ := sInf {k : ℕ | n ≤ k^3}

lemma n_in_K_set (n : ℕ) : n ∈ {k : ℕ | n ≤ k^3} := by
  simp only [Set.mem_setOf_eq]
  cases n with
  | zero => rfl
  | succ m =>
    have h : Nat.succ m ≤ (Nat.succ m)^3 := by
      calc Nat.succ m = (Nat.succ m) * 1 := by ring
        _ ≤ (Nat.succ m) * ((Nat.succ m) * (Nat.succ m)) := by
          apply Nat.mul_le_mul_left
          nlinarith
        _ = (Nat.succ m)^3 := by ring
    exact h

lemma n_le_K_cube (n : ℕ) : n ≤ (K n)^3 := by
  have h := Nat.sInf_mem (Set.nonempty_of_mem (n_in_K_set n))
  exact h

lemma K_le_n (n : ℕ) : K n ≤ n := by
  have h := Nat.sInf_le (n_in_K_set n)
  exact h

lemma pow_K_le_pow_n (n : ℕ) (hn : 10 ≤ K n) : (K n)^3 ≤ 2^(K n) := by
  exact n_le_two_pow_cbrt (K n) hn

lemma primeCounting_mono {a b : ℕ} (h : a ≤ b) : Nat.primeCounting a ≤ Nat.primeCounting b := by
  use a.monotone_primeCounting h

lemma pow_two_le_pow_pi (n : ℕ) (hn : 2 ≤ n) : 2^(n / 2) ≤ n ^ (Nat.primeCounting n) := by
  let m := n / 2
  have h_m_pos : 1 ≤ m := Nat.div_pos hn (by omega)
  have h1 : 2^m ≤ (2 * m) ^ (Nat.primeCounting (2 * m)) := two_pow_le_pow_primeCounting m
  have h2 : 2 * m ≤ n := Nat.mul_div_le n 2
  have h3 : Nat.primeCounting (2 * m) ≤ Nat.primeCounting n := primeCounting_mono h2
  have h4 : (2 * m) ^ (Nat.primeCounting (2 * m)) ≤ n ^ (Nat.primeCounting n) := by
    calc (2 * m) ^ (Nat.primeCounting (2 * m)) ≤ n ^ (Nat.primeCounting (2 * m)) := Nat.pow_le_pow_left h2 (Nat.primeCounting (2 * m))
      _ ≤ n ^ (Nat.primeCounting n) := Nat.pow_le_pow_right (by omega) h3
  exact le_trans h1 h4

lemma exp_bound1 (n : ℕ) (hn : 16 ≤ n) : n * n ≤ 2^n := by
  exact (16).le_induction (by decide) ( fun and A B=>pow_succ (2) and▸by linarith[mul_le_mul_left' A and]) n hn

lemma exp_bound2 (n : ℕ) (hn : 64 ≤ n) : n^3 ≤ 2^n := by
  exact (64).le_induction (by decide) ( fun and K V' =>pow_succ (2) and▸by nlinarith only[ K,pow_three and▸V']) n ↑hn

lemma K_bound_contradiction (K_val : ℕ) (hK : 200 ≤ K_val) : K_val ^ (3 * K_val * K_val) < 2 ^ ((K_val - 1) ^ 3 / 2) := by
  use match K_val with | S+1=>by_contra fun and=>absurd ((.log (S+1)-2*Real.log 2).add_one_le_exp) ?_
  push_cast[←@Nat.cast_lt ℝ,Real.exp_sub, two_mul,Real.exp_add,Real.exp_log S.cast_add_one_pos,Real.exp_log two_pos,←Real.rpow_natCast,Real.exp_lt_exp,Real.rpow_def_of_pos S.cast_add_one_pos]
  push_cast[←@Nat.cast_lt ℝ,←Real.rpow_natCast,Real.exp_lt_exp,Real.rpow_def_of_pos S.cast_add_one_pos,Real.rpow_def_of_pos two_pos]at*
  obtain ⟨s, rfl⟩| ⟨a, rfl⟩:= S.even_or_odd
  · simp_all[←two_mul,pow_three, false,mul_assoc]
    have := (.log (2 *s+1)-Real.log 2*3-.log 2-.log 2).add_one_le_exp
    simp_rw [ Real.exp_sub, (2 *s+1:ℝ).exp_log (by positivity),Real.exp_mul,Real.exp_log two_pos] at this
    nlinarith only [mul_nonneg s.cast_nonneg (sq_nonneg (s-99 :ℝ)),Real.log_two_gt_d9,show (199:ℝ) ≤2*s by norm_cast, this, and]
  ring_nf at *
  norm_num[Nat.add_mod,Nat.add_div,Nat.mul_mod,Nat.mul_div_assoc]at*
  rw[<-sub_lt_iff_lt_add']
  have := (.log (1+(1+a*2))-Real.log 2*3-.log 2-.log 2-.log 2).add_one_le_exp
  simp_rw [Real.exp_sub _,(1 +(1+a*2 :ℝ)).exp_log (by. (positivity)), Real.exp_mul,Real.exp_log two_pos] at this
  nlinarith[Real.log_two_gt_d9,Real.log_two_lt_d9,show (199: ℝ) ≤ 1+a*2by norm_cast, (by bound: (0: ℝ) ≤ a^3)]

lemma K_minus_one_cube_lt_n (n : ℕ) (h : 1 ≤ K n) : (K n - 1)^3 < n := by
  by_contra h_not
  push_neg at h_not
  have h_in : (K n - 1) ∈ {k : ℕ | n ≤ k^3} := by
    simp only [Set.mem_setOf_eq]
    exact h_not
  have h_le := Nat.sInf_le h_in
  have h_K_def : K n = sInf {k : ℕ | n ≤ k^3} := rfl
  rw [←h_K_def] at h_le
  omega

lemma pi_pos (n : ℕ) (hn : 2 ≤ n) : 1 ≤ Nat.primeCounting n := by
  exact (Nat.count_eq_card_filter_range _ _).ge.trans'.comp Finset.card_pos.mpr ⟨2,by ·norm_num[hn]⟩

lemma M_bound_strong : ∃ C : ℕ, ∀ n : ℕ, 2 ≤ n → (K n)^2 ≤ C * Nat.primeCounting n := by
  use 40000
  intro n hn
  by_cases hK : K n < 200
  · have h_pi : 1 ≤ Nat.primeCounting n := pi_pos n hn
    have h_K2 : (K n)^2 ≤ 40000 := by
      calc (K n)^2 = (K n) * (K n) := by ring
        _ ≤ 199 * 199 := Nat.mul_le_mul (Nat.le_of_lt_succ hK) (Nat.le_of_lt_succ hK)
        _ ≤ 40000 := by norm_num
    calc (K n)^2 ≤ 40000 := h_K2
      _ = 40000 * 1 := by ring
      _ ≤ 40000 * Nat.primeCounting n := Nat.mul_le_mul_left 40000 h_pi
  · push_neg at hK
    by_contra h_contra
    push_neg at h_contra
    have h_pi_le : Nat.primeCounting n ≤ (K n)^2 := by omega
    have h2 : 2 ^ (n / 2) ≤ n ^ (Nat.primeCounting n) := pow_two_le_pow_pi n hn
    have h_n_le : n ≤ (K n)^3 := n_le_K_cube n
    have h_K_pos : 1 ≤ K n := by omega
    have h3 : n ^ (Nat.primeCounting n) ≤ ((K n)^3) ^ ((K n)^2) := by
      calc n ^ (Nat.primeCounting n) ≤ ((K n)^3) ^ (Nat.primeCounting n) := Nat.pow_le_pow_left h_n_le _
        _ ≤ ((K n)^3) ^ ((K n)^2) := Nat.pow_le_pow_right (by omega) h_pi_le
    have h4 : ((K n)^3) ^ ((K n)^2) = (K n) ^ (3 * (K n) * (K n)) := by
      calc ((K n)^3) ^ ((K n)^2) = (K n) ^ (3 * (K n)^2) := (Nat.pow_mul (K n) 3 ((K n)^2)).symm
        _ = (K n) ^ (3 * (K n) * (K n)) := by ring
    have h5 : 2 ^ (n / 2) ≤ (K n) ^ (3 * (K n) * (K n)) := by
      calc 2 ^ (n / 2) ≤ n ^ (Nat.primeCounting n) := h2
        _ ≤ ((K n)^3) ^ ((K n)^2) := h3
        _ = (K n) ^ (3 * (K n) * (K n)) := h4
    have h_K_minus_one : (K n - 1)^3 < n := K_minus_one_cube_lt_n n h_K_pos
    have h6 : ((K n - 1)^3) / 2 ≤ n / 2 := Nat.div_le_div_right (le_of_lt h_K_minus_one)
    have h7 : 2 ^ (((K n - 1)^3) / 2) ≤ 2 ^ (n / 2) := Nat.pow_le_pow_right (by omega) h6
    have h8 : 2 ^ (((K n - 1)^3) / 2) ≤ (K n) ^ (3 * (K n) * (K n)) := le_trans h7 h5
    have h9 : (K n) ^ (3 * (K n) * (K n)) < 2 ^ (((K n - 1)^3) / 2) := K_bound_contradiction (K n) hK
    omega

noncomputable def M (n : ℕ) : ℕ := (K n)^2
noncomputable def S_set (n : ℕ) : Finset ℕ :=
  (Finset.filter Nat.Prime (Finset.Icc 1 n)) ∪ (Finset.Icc 1 (min n (M n)))

lemma smooth_factorization (x A B K_val : ℕ) (hx0 : 0 < x) (hA0 : 0 < A) (hB0 : 0 < B) (hK0 : 0 < K_val)
    (h_prime : ∀ p, p.Prime → p ∣ x → p ≤ K_val)
    (h_bound : x * K_val ≤ A * B) :
    ∃ a b : ℕ, x = a * b ∧ a ≤ A ∧ b ≤ B := by
  let S_div := (Nat.divisors x).filter (fun d => d ≤ A)
  have h1_in : 1 ∈ S_div := by
    simp only [S_div, Finset.mem_filter, Nat.mem_divisors, ne_eq, hx0.ne', not_false_eq_true, and_true]
    exact ⟨Nat.one_dvd x, hA0⟩
  have h_nonempty : S_div.Nonempty := ⟨1, h1_in⟩
  let a := S_div.max' h_nonempty
  have ha_in : a ∈ S_div := Finset.max'_mem S_div h_nonempty
  have ha_div : a ∣ x := by
    have := Finset.mem_filter.mp ha_in
    exact Nat.dvd_of_mem_divisors this.1
  have ha_le : a ≤ A := by
    have := Finset.mem_filter.mp ha_in
    exact this.2
  have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha_div hx0
  let b := x / a
  have hx_eq : x = a * b := (Nat.mul_div_cancel' ha_div).symm
  use a, b
  refine ⟨hx_eq, ha_le, ?_⟩
  by_contra h_b_gt
  push_neg at h_b_gt
  have hb_gt_1 : b > 1 := by omega
  have hex_p : ∃ p, p.Prime ∧ p ∣ b := Nat.exists_prime_and_dvd hb_gt_1.ne'
  rcases hex_p with ⟨p, hp_prime, hp_dvd_b⟩
  have hp_dvd_x : p ∣ x := by
    rw [hx_eq]
    exact dvd_mul_of_dvd_right hp_dvd_b a
  have hp_le_K : p ≤ K_val := h_prime p hp_prime hp_dvd_x
  let a' := a * p
  have ha'_div : a' ∣ x := by
    rcases hp_dvd_b with ⟨c, hc⟩
    have : x = a * (p * c) := by
      calc
        x = a * b := hx_eq
        _ = a * (p * c) := by rw [hc]
    rw [this, ← mul_assoc]
    exact dvd_mul_right (a * p) c
  have ha'_gt_A : a' > A := by
    by_contra h_not_gt
    push_neg at h_not_gt
    have ha'_in : a' ∈ S_div := by
      simp only [S_div, Finset.mem_filter, Nat.mem_divisors, ne_eq, hx0.ne', not_false_eq_true, and_true]
      exact ⟨ha'_div, h_not_gt⟩
    have ha'_le_a : a' ≤ a := Finset.le_max' S_div a' ha'_in
    have hp_ge_2 : p ≥ 2 := hp_prime.two_le
    have h_ap_gt_a : a < a * p := by
      calc
        a < a + a := by omega
        _ = a * 2 := by ring
        _ ≤ a * p := Nat.mul_le_mul_left a hp_ge_2
    omega
  have h_b_ge : b ≥ B + 1 := h_b_gt
  have h_ap_ge : a * p ≥ A + 1 := ha'_gt_A
  have h_aK_ge : a * K_val ≥ A + 1 := by
    have : a * p ≤ a * K_val := Nat.mul_le_mul_left a hp_le_K
    omega
  have h_xK : x * K_val = (a * K_val) * b := by
    calc
      x * K_val = (a * b) * K_val := by rw [hx_eq]
      _ = a * K_val * b := by ac_rfl
  have h_xK_gt : x * K_val > A * B := by
    calc
      x * K_val = (a * K_val) * b := h_xK
      _ ≥ (A + 1) * (B + 1) := Nat.mul_le_mul h_aK_ge h_b_ge
      _ = A * B + A + B + 1 := by ring
      _ > A * B := by omega
  omega

lemma card_S_set (n : ℕ) : (S_set n).card ≤ Nat.primeCounting n + M n := by
  rw [←add_comm, S_set, M,Nat.primeCounting, Finset.card_eq_sum_ones]
  exact ( Finset.card_eq_sum_ones _)▸.trans ( Finset.card_union_le _ _) (Nat.add_comm _ _▸Nat.add_le_add ((1).card_Icc _▸inf_le_right) (( Finset.card_mono fun and=>by simp_all[le_of_lt]).trans (Nat.count_eq_card_filter_range _ _).ge))

lemma S_set_valid (n : ℕ) (hn : 2 ≤ n) : Finset.Icc 1 n ⊆ set_prod (S_set n) := by
  intro x hx
  have hx_mem := Finset.mem_Icc.mp hx
  have hx_pos : 0 < x := hx_mem.1
  have hx_le : x ≤ n := hx_mem.2
  have h1_in_S : 1 ∈ S_set n := by
    rw [S_set, Finset.mem_union, Finset.mem_Icc]
    right
    have h1_n : 1 ≤ n := by omega
    have h1_M : 1 ≤ M n := by
      unfold M
      have hk1 : 1 ≤ K n := by
        by_contra h
        push_neg at h
        have hk0 : K n = 0 := by omega
        have hn_le : n ≤ (K n)^3 := n_le_K_cube n
        rw [hk0] at hn_le
        omega
      nlinarith
    exact ⟨by omega, le_min h1_n h1_M⟩
  by_cases h_xM : x ≤ M n
  · have hx_in_S : x ∈ S_set n := by
      rw [S_set, Finset.mem_union, Finset.mem_Icc]
      right
      exact ⟨hx_mem.1, le_min hx_le h_xM⟩
    rw [set_prod, Finset.mem_image]
    use (x, 1)
    refine ⟨Finset.mem_product.mpr ⟨hx_in_S, h1_in_S⟩, by ring⟩
  · push_neg at h_xM
    have hx_gt_M : x > M n := h_xM
    have hK0 : 0 < K n := by
      by_contra h
      push_neg at h
      have hk0 : K n = 0 := by omega
      have hn_le : n ≤ (K n)^3 := n_le_K_cube n
      rw [hk0] at hn_le
      omega
    have h_smooth_or_not : (∃ p, p.Prime ∧ p ∣ x ∧ K n < p) ∨ (∀ p, p.Prime → p ∣ x → p ≤ K n) := by
      by_cases h : ∃ p, p.Prime ∧ p ∣ x ∧ K n < p
      · left; exact h
      · right; push_neg at h; exact h
    cases h_smooth_or_not with
    | inl h =>
      rcases h with ⟨p, hp_prime, hp_div, hp_gt⟩
      have hp_in_S : p ∈ S_set n := by
        rw [S_set, Finset.mem_union, Finset.mem_filter]
        left
        have hp_le_x : p ≤ x := Nat.le_of_dvd hx_pos hp_div
        exact ⟨Finset.mem_Icc.mpr ⟨Nat.Prime.pos hp_prime, le_trans hp_le_x hx_le⟩, hp_prime⟩
      let y := x / p
      have hy_in_S : y ∈ S_set n := by
        rw [S_set, Finset.mem_union, Finset.mem_Icc]
        right
        have hy_pos : 0 < y := by
          have hp_pos : 0 < p := Nat.Prime.pos hp_prime
          exact Nat.div_pos (Nat.le_of_dvd hx_pos hp_div) hp_pos
        have hy_le_n : y ≤ n := by
          calc y = x / p := rfl
            _ ≤ x := Nat.div_le_self x p
            _ ≤ n := hx_le
        have hy_le_M : y ≤ M n := by
          by_contra hy_gt
          push_neg at hy_gt
          have h_x_eq1 : x = p * y := (Nat.mul_div_cancel' hp_div).symm
          have h_x_eq : x = y * p := by
            calc x = p * y := h_x_eq1
              _ = y * p := mul_comm p y
          have h_M_def : M n = (K n)^2 := rfl
          have h_x_gt : (K n)^3 < x := by
            calc (K n)^3 = (M n) * (K n) := by rw [h_M_def]; ring
              _ ≤ y * (K n) := Nat.mul_le_mul_right (K n) (by omega)
              _ < y * p := Nat.mul_lt_mul_of_pos_left hp_gt hy_pos
              _ = x := h_x_eq.symm
          have hn_le_K : n ≤ (K n)^3 := n_le_K_cube n
          omega
        exact ⟨hy_pos, le_min hy_le_n hy_le_M⟩
      rw [set_prod, Finset.mem_image]
      use (p, y)
      have h_x_eq1 : x = p * y := (Nat.mul_div_cancel' hp_div).symm
      refine ⟨Finset.mem_product.mpr ⟨hp_in_S, hy_in_S⟩, h_x_eq1.symm⟩
    | inr h =>
      have hx_K : x * (K n) ≤ (M n) * (M n) := by
        calc x * (K n) ≤ n * (K n) := Nat.mul_le_mul_right (K n) hx_le
          _ ≤ (K n)^3 * (K n) := Nat.mul_le_mul_right (K n) (n_le_K_cube n)
          _ = (K n)^2 * (K n)^2 := by ring
          _ = (M n) * (M n) := rfl
      have hM0 : 0 < M n := by unfold M; nlinarith
      have ⟨a, b, hx_eq, ha_le, hb_le⟩ := smooth_factorization x (M n) (M n) (K n) hx_pos hM0 hM0 hK0 h hx_K
      have ha_in_S : a ∈ S_set n := by
        rw [S_set, Finset.mem_union, Finset.mem_Icc]
        right
        have ha_pos : 0 < a := by
          by_contra ha_zero
          have ha_zero' : a = 0 := by omega
          have hx_zero : x = 0 := by
            calc x = a * b := hx_eq
              _ = 0 * b := by rw [ha_zero']
              _ = 0 := by ring
          omega
        have hb_pos : 0 < b := by
          by_contra hb_zero
          have hb_zero' : b = 0 := by omega
          have hx_zero : x = 0 := by rw [hx_eq, hb_zero', mul_zero]
          omega
        have ha_le_n : a ≤ n := by
          have h_ax : a ≤ x := by
            have h_a_ab : a ≤ a * b := Nat.le_mul_of_pos_right a hb_pos
            rw [←hx_eq] at h_a_ab
            exact h_a_ab
          calc a ≤ x := h_ax
            _ ≤ n := hx_le
        exact ⟨ha_pos, le_min ha_le_n ha_le⟩
      have hb_in_S : b ∈ S_set n := by
        rw [S_set, Finset.mem_union, Finset.mem_Icc]
        right
        have hb_pos : 0 < b := by
          by_contra hb_zero
          have hb_zero' : b = 0 := by omega
          have hx_zero : x = 0 := by rw [hx_eq, hb_zero', mul_zero]
          omega
        have ha_pos : 0 < a := by
          by_contra ha_zero
          have ha_zero' : a = 0 := by omega
          have hx_zero : x = 0 := by rw [hx_eq, ha_zero', zero_mul]
          omega
        have hb_le_n : b ≤ n := by
          have h_bx : b ≤ x := by
            have h_b_ab : b ≤ a * b := Nat.le_mul_of_pos_left b ha_pos
            rw [←hx_eq] at h_b_ab
            exact h_b_ab
          calc b ≤ x := h_bx
            _ ≤ n := hx_le
        exact ⟨hb_pos, le_min hb_le_n hb_le⟩
      rw [set_prod, Finset.mem_image]
      use (a, b)
      refine ⟨Finset.mem_product.mpr ⟨ha_in_S, hb_in_S⟩, hx_eq.symm⟩

lemma a_le_card_S (n : ℕ) (hn : 2 ≤ n) : a n ≤ (S_set n).card := by
  have hn0 : n ≠ 0 := by omega
  unfold a
  split_ifs with h
  · contradiction
  · have h_valid : S_set n ∈ (Finset.Icc 1 n).powerset.filter (fun S => Finset.Icc 1 n ⊆ set_prod S) := by
      rw [Finset.mem_filter]
      refine ⟨?_, S_set_valid n hn⟩
      norm_num[S_set]
      refine Finset.union_subset ↑( Finset.filter_subset _ _) (Finset.Icc_subset_Icc_right ↑inf_le_left)
    use Finset.min'_le _ _ (( Finset.mem_image_of_mem _) h_valid)

lemma M_bound : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → (M n : ℝ) ≤ C * Nat.primeCounting n := by
  have h := M_bound_strong
  rcases h with ⟨C, hC⟩
  use C
  intro n hn
  have hCn := hC n hn
  exact_mod_cast hCn

-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → (a n : ℝ) / (Nat.primeCounting n : ℝ) ≤ C := by
  -- EVOLVE-BLOCK-START
  have hM := M_bound
  rcases hM with ⟨CM, hCM⟩
  use 1 + CM
  intro n hn
  have h_a_le := a_le_card_S n hn
  have h_card_le := card_S_set n
  have h_pi_pos : 0 < (Nat.primeCounting n : ℝ) := by norm_num [Nat.primeCounting, Finset.Nonempty,hn]
                                                      exact (Nat.count_eq_card_filter_range _ _).ge.trans'.comp Finset.card_pos.mpr ⟨2,List.mem_filter.mpr (by exists Finset.mem_range_succ_iff.mpr hn)⟩
  have h_M_le : (M n : ℝ) ≤ CM * Nat.primeCounting n := hCM n hn
  exact (div_le_iff₀ h_pi_pos).mpr ((Nat.cast_le.mpr (h_a_le.trans h_card_le)).trans (.trans (by rw [Nat.cast_add]) (by linear_combination h_M_le)))
  -- EVOLVE-BLOCK-END
