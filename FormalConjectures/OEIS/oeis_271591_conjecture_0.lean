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




open Nat

/--
The Tribonacci numbers $T_n$ (A000073).
$T_0=0, T_1=0, T_2=1$, and $T_n = T_{n-1} + T_{n-2} + T_{n-3}$ for $n \ge 3$.
-/
def tribonacci (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => (tribonacci (n + 2)) + (tribonacci (n + 1)) + (tribonacci n)

/--
A271591: Second most significant bit of the tribonacci number A000073(n).
This is formalized by extracting the bit at position $\lfloor \log_2 T_n \rfloor - 1$.
-/
def a (n : ℕ) : ℕ :=
  let T := tribonacci n
  -- The index of the MSB is T.log2. The index of the second MSB is T.log2 - 1.
  if h : T ≤ 1 then
    0
  else
    let j_smsb : ℕ := T.log2 - 1
    if T.testBit j_smsb then 1 else 0

def is_maximal_run (v : ℕ) (n L : ℕ) : Prop :=
  n ≥ 2 ∧ L ≥ 1 ∧
  -- The run consists of L consecutive $v$'s starting at n
  (∀ i : ℕ, i < L → a (n + i) = v) ∧
  -- The run is not followed by $v$
  (a (n + L) ≠ v) ∧
  -- The run is not preceded by $v$
  (a (n - 1) ≠ v)

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
def valid_bounds (n : ℕ) : Prop :=
  183 * tribonacci n ≤ 100 * tribonacci (n + 1) ∧
  100 * tribonacci (n + 1) ≤ 185 * tribonacci n

lemma k_unique_0 (k k' B : ℕ)
  (h1 : 4 * 2^k ≤ B) (h2 : B < 8 * 2^k)
  (h3 : 2 * 2^k' ≤ B) (h4 : B < 3 * 2^k') : k' = k + 1 := by
  exact (le_antisymm (not_lt.mp (by valid ∘ (2).pow_le_pow_right (by decide)))) ((2).pow_lt_pow_iff_right (by constructor) |>.mp (by valid))

lemma k_unique_1 (k k' B : ℕ)
  (h1 : 3 * 2^k ≤ B) (h2 : B < 6 * 2^k)
  (h3 : 3 * 2^k' ≤ B) (h4 : B < 4 * 2^k') : k' = k := by
  exact (le_antisymm_iff.mpr (by repeat use not_lt.mp (by valid ∘(@2).pow_le_pow_right (by decide))))

lemma k_unique_C (k k'' C : ℕ)
  (h1 : 7 * 2^k ≤ C) (h2 : C < 12 * 2^k)
  (h3 : 2 * 2^k'' ≤ C) (h4 : C < 3 * 2^k'') : k'' = k + 2 := by
  exact (le_antisymm (not_lt.mp (by valid ∘ ((2).pow_le_pow_right (by decide) ·|>.trans' (pow_add _ _ @3).ge))) ((2).pow_lt_pow_iff_right (by constructor) |>.mp (by valid)))

lemma k_unique_C1 (k k'' C : ℕ)
  (h1 : 5 * 2^k ≤ C) (h2 : C < 8 * 2^k)
  (h3 : 3 * 2^k'' ≤ C) (h4 : C < 4 * 2^k'') : k'' = k + 1 := by
  exact (le_antisymm (not_lt.1 (by valid ∘(2).pow_le_pow_right (by decide))) ((2).pow_lt_pow_iff_right (by decide) |>.mp (by valid)))

lemma a_eq_1_prop_k (n : ℕ) (hT : tribonacci n > 1) (ha : a n = 1) :
  ∃ k, 3 * 2^k ≤ tribonacci n ∧ tribonacci n < 4 * 2^k := by
  delta a at ha
  simp_all -contextual[Nat.log2_eq_log_two, dif_neg,Nat.testBit]
  induction(1).exists_eq_add_of_le' ((2).log_pos (by constructor) hT)
  simp_all[Nat.log_eq_iff,Nat.shiftRight_eq_div_pow,pow_add]
  exact ⟨by valid,by_contra fun and=>by cases ha.symm.trans (by rw [(Nat.div_eq_of_lt_le (by valid) (by valid):_/_=2)])⟩

lemma a_eq_0_prop_k (n : ℕ) (hT : tribonacci n > 1) (ha : a n = 0) :
  ∃ k, 2 * 2^k ≤ tribonacci n ∧ tribonacci n < 3 * 2^k := by
  change star @_ = _ at ha
  simp_all -contextual [Nat.log2_eq_log_two,Nat.decLe,Nat.testBit]
  simp_all[mul_comm (3), dif_neg,Nat.succ_le,Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt ∘Nat.div_lt_of_lt_mul,←pow_succ',Nat.pow_log_le_self,ne_zero_of_lt hT,Nat.lt_pow_succ_log_self]
  cases(1).exists_eq_add_of_le' ((2).log_pos (by decide) hT)
  simp_all[(2).log_eq_iff]
  exact ⟨ _, (by valid:).imp_right fun and=>not_le.1 (by cases ha.symm.trans<|by rw [le_antisymm (Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by valid)))<|(Nat.le_div_iff_mul_le (by valid)).2.comp (mul_comm _ _).trans_le ·])⟩

lemma prop_implies_a_eq_1_k (n k : ℕ) (hT : tribonacci n > 1)
  (h1 : 3 * 2^k ≤ tribonacci n) (h2 : tribonacci n < 4 * 2^k) : a n = 1 := by
  simp_rw [a,.> ·] at hT⊢
  norm_num[*, dif_neg,Nat.log_eq_of_pow_le_of_lt_pow (.trans (Nat.le_mul_of_pos_left _ _) h1),Nat.log2_eq_log_two,Nat.testBit]
  push_cast[Nat.log_eq_of_pow_le_of_lt_pow (by valid:2^ (k + 1)≤ tribonacci n) (by valid), (Nat.div_eq_of_lt_le (by valid) (by valid): tribonacci n/2^k=3),Nat.shiftRight_eq_div_pow]

lemma prop_implies_a_eq_0_k (n k : ℕ) (hT : tribonacci n > 1)
  (h1 : 2 * 2^k ≤ tribonacci n) (h2 : tribonacci n < 3 * 2^k) : a n = 0 := by
  rw [←pow_succ',gt_iff_lt, a] at*
  norm_num [Nat.log_eq_of_pow_le_of_lt_pow h1 (by valid),Nat.log2_eq_log_two, false,Nat.succ_sub_one _,Nat.testBit]
  norm_num [Nat.shiftRight_eq_div_pow, false,Nat.div_eq_of_lt_le.comp (pow_succ' _ _).ge.trans h1 h2]

lemma valid_bounds_step (A B C : ℕ)
  (h1 : 183 * A ≤ 100 * B ∧ 100 * B ≤ 185 * A)
  (h2 : 183 * B ≤ 100 * C ∧ 100 * C ≤ 185 * B) :
  183 * C ≤ 100 * (C + B + A) ∧ 100 * (C + B + A) ≤ 185 * C := by
  grind

lemma valid_bounds_step_n (n : ℕ) (h1 : valid_bounds n) (h2 : valid_bounds (n + 1)) : valid_bounds (n + 2) := by
  have step := valid_bounds_step (tribonacci n) (tribonacci (n + 1)) (tribonacci (n + 2)) h1 h2
  have h_eq : tribonacci (n + 3) = tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n := rfl
  trivial

lemma valid_bounds_7 : valid_bounds 7 := by
  norm_num [ valid_bounds]
  norm_num only [ tribonacci, and_self]

lemma valid_bounds_8 : valid_bounds 8 := by
  show 0 ∈ {s |_}
  norm_num only [ tribonacci,Set.mem_setOf, and_self]

lemma valid_bounds_all_ind (n : ℕ) : valid_bounds (n + 7) ∧ valid_bounds (n + 8) := by
  induction n with
  | zero =>
    norm_num[valid_bounds]
    trivial
  | succ n ih =>
    simp_all only [valid_bounds, and_self]
    rw[ tribonacci]
    grind[ tribonacci]

lemma valid_bounds_all (n : ℕ) (h : n ≥ 7) : valid_bounds n := by
  delta valid_bounds
  delta tribonacci Real
  exact n.sub_add_cancel h▸(n-7).strongRec fun and x=>match and with|0|1|2=>by decide | S+3=>(x (S+2) (by constructor)).elim ((x (S+1) (by valid)).elim ((x S (by valid)).elim (by (fin_omega))))

lemma trib_gt_1 (n : ℕ) (hn : n ≥ 6) : tribonacci n > 1 := by
  delta tribonacci
  exact (hn).rec (by decide) fun and μ=>match(‹ℕ›:) with | S+3=>μ.trans_le.comp (le_add_right) le_self_add

lemma trib_eq_shift (n : ℕ) (hn : n ≥ 1) : tribonacci (n + 2) = tribonacci (n + 1) + tribonacci n + tribonacci (n - 1) := by
  have : n + 2 = n - 1 + 3 := by omega
  rw [this, tribonacci]
  have h1 : n - 1 + 2 = n + 1 := by omega
  have h2 : n - 1 + 1 = n := by omega
  rw [h1, h2]

lemma trib_expand (A B C T2 T3 T4 T5 : ℕ)
  (h2 : T2 = C + B + A)
  (h3 : T3 = T2 + C + B)
  (h4 : T4 = T3 + T2 + C)
  (h5 : T5 = T4 + T3 + T2) :
  T2 = A + B + C ∧
  T3 = A + 2 * B + 2 * C ∧
  T4 = 2 * A + 3 * B + 4 * C ∧
  T5 = 4 * A + 6 * B + 7 * C := by omega

lemma a_dichotomy (n : ℕ) : a n = 0 ∨ a n = 1 := by
  norm_num[a, or_iff_not_imp_left]
  use (if_neg ·.not_ge▸if_pos ·)

lemma run_0_a_n1 (A B C P : ℕ)
  (hA1 : 3 * P ≤ A) (hA2 : A < 4 * P)
  (hB1 : 4 * P ≤ B) (hB2 : B < 6 * P)
  (hAB1 : 183 * A ≤ 100 * B) (hAB2 : 100 * B ≤ 185 * A)
  (hBC1 : 183 * B ≤ 100 * C) (hBC2 : 100 * C ≤ 185 * B) :
  8 * P ≤ C ∧ C < 12 * P := by
  grind

lemma run_1_a_n1 (A B C P : ℕ)
  (hA1 : 2 * P ≤ A) (hA2 : A < 3 * P)
  (hB1 : 3 * P ≤ B) (hB2 : B < 4 * P)
  (hAB1 : 183 * A ≤ 100 * B) (hAB2 : 100 * B ≤ 185 * A)
  (hBC1 : 183 * B ≤ 100 * C) (hBC2 : 100 * C ≤ 185 * B) :
  6 * P ≤ C ∧ C < 8 * P := by
  omega

lemma run_0_bounds (A B C P : ℕ)
  (hA1 : 3 * P ≤ A) (hA2 : A < 4 * P)
  (hB1 : 4 * P ≤ B) (hB2 : B < 6 * P)
  (hC1 : 8 * P ≤ C) (hC2 : C < 12 * P)
  (hAB1 : 183 * A ≤ 100 * B) (hAB2 : 100 * B ≤ 185 * A)
  (hBC1 : 183 * B ≤ 100 * C) (hBC2 : 100 * C ≤ 185 * B) :
  let x2 := A + B + C
  let x3 := A + 2 * B + 2 * C
  let x4 := 2 * A + 3 * B + 4 * C
  let x5 := 4 * A + 6 * B + 7 * C
  16 * P ≤ x2 ∧ x2 < 24 * P ∧
  32 * P ≤ x3 ∧ x3 < 48 * P ∧
  48 * P ≤ x4 ∧ x4 < 96 * P ∧
  (x4 ≥ 64 * P → 96 * P ≤ x5 ∧ x5 < 128 * P) := by
  grind

lemma run_1_bounds (A B C P : ℕ)
  (hA1 : 2 * P ≤ A) (hA2 : A < 3 * P)
  (hB1 : 3 * P ≤ B) (hB2 : B < 4 * P)
  (hC1 : 6 * P ≤ C) (hC2 : C < 8 * P)
  (hAB1 : 183 * A ≤ 100 * B) (hAB2 : 100 * B ≤ 185 * A)
  (hBC1 : 183 * B ≤ 100 * C) (hBC2 : 100 * C ≤ 185 * B) :
  let x2 := A + B + C
  let x3 := A + 2 * B + 2 * C
  let x4 := 2 * A + 3 * B + 4 * C
  12 * P ≤ x2 ∧ x2 < 16 * P ∧
  16 * P ≤ x3 ∧ x3 < 32 * P ∧
  (x3 ≥ 24 * P → 32 * P ≤ x4 ∧ x4 < 48 * P) := by
  grind

lemma small_cases_0 (n L : ℕ) (hn : n < 9) (h : is_maximal_run 0 n L) : False := by
  norm_num[is_maximal_run]at @h
  use absurd (h.2.2.1 0 h.2.1) fun and=>by match n with | S+9=>omega

lemma small_cases_1 (n L : ℕ) (hn : n < 9) (h : is_maximal_run 1 n L) : L = 3 ∨ L = 4 := by
  rcases ↑h
  simp_all[a]
  use (by valid:).2.elim fun and b=>by_contra fun and' =>absurd (and 0) fun and' =>absurd (and 1) fun and' =>absurd (and 2) fun and' =>absurd (and (3)) (absurd (and 4) ∘? _)
  interval_cases n
  · simp_all![Nat.succ_le]
  · simp_all!
  · simp_all!
  · match L with | S+5=>simp_all!+decide[Nat.log2]
  · match L with | S+5=>norm_num+decide[ tribonacci,Nat.log2_eq_log_two]
  · match L with|1|2=>norm_num+decide[ tribonacci,Nat.log2]at* | S+5=>norm_num+decide[ tribonacci,Nat.log2]at and'
  · match L with|1|2=>norm_num+decide[ tribonacci,Nat.log2_eq_log_two]at* | S+5=>norm_num+decide[ tribonacci,Nat.log2_eq_log_two]

lemma run_0_main (n L : ℕ) (hn : n ≥ 9) (h : is_maximal_run 0 n L) : L = 4 ∨ L = 5 := by
  rcases h with ⟨hn_ge_2, hL_ge_1, h_run, h_after, h_before⟩
  have ht_m1 : tribonacci (n - 1) > 1 := trib_gt_1 (n - 1) (by omega)
  have ht_0 : tribonacci n > 1 := trib_gt_1 n (by omega)
  have ht_1 : tribonacci (n + 1) > 1 := trib_gt_1 (n + 1) (by omega)
  have ht_2 : tribonacci (n + 2) > 1 := trib_gt_1 (n + 2) (by omega)
  have ht_3 : tribonacci (n + 3) > 1 := trib_gt_1 (n + 3) (by omega)
  have ht_4 : tribonacci (n + 4) > 1 := trib_gt_1 (n + 4) (by omega)
  have ht_5 : tribonacci (n + 5) > 1 := trib_gt_1 (n + 5) (by omega)
  have ha_m1 : a (n - 1) = 1 := by
    have hd := a_dichotomy (n - 1)
    tauto
  have ha_0 : a n = 0 := h_run 0 (by omega)
  have hk : ∃ k, 3 * 2^k ≤ tribonacci (n - 1) ∧ tribonacci (n - 1) < 4 * 2^k := a_eq_1_prop_k (n - 1) ht_m1 ha_m1
  rcases hk with ⟨k, hk1, hk2⟩
  set P := 2^k
  set A := tribonacci (n - 1)
  set B := tribonacci n
  set C := tribonacci (n + 1)
  have hB_bounds_raw := valid_bounds_all (n - 1) (by omega)
  have hB_bounds : 183 * A ≤ 100 * B ∧ 100 * B ≤ 185 * A := by
    dsimp [valid_bounds] at hB_bounds_raw
    have : n - 1 + 1 = n := by omega
    rw [this] at hB_bounds_raw
    exact hB_bounds_raw
  have hk0_b : B < 8 * P := by omega
  have hk0_a : 4 * P ≤ B := by omega
  have hk_B : ∃ k', 2 * 2^k' ≤ B ∧ B < 3 * 2^k' := a_eq_0_prop_k n ht_0 ha_0
  rcases hk_B with ⟨k', hk'1, hk'2⟩
  have h_k' : k' = k + 1 := k_unique_0 k k' B hk0_a hk0_b hk'1 hk'2
  have hB_exact : 4 * P ≤ B ∧ B < 6 * P := by
    subst h_k'
    have hp1 : 2^(k+1) = 2 * P := by dsimp [P]; rw [pow_add, pow_one, mul_comm]
    omega
  have hC_bounds_raw := valid_bounds_all n (by omega)
  have hC_bounds : 183 * B ≤ 100 * C ∧ 100 * C ≤ 185 * B := by
    dsimp [valid_bounds] at hC_bounds_raw
    exact hC_bounds_raw
  have hC_exact : 8 * P ≤ C ∧ C < 12 * P := run_0_a_n1 A B C P hk1 hk2 hB_exact.1 hB_exact.2 hB_bounds.1 hB_bounds.2 hC_bounds.1 hC_bounds.2
  have ha_1 : a (n + 1) = 0 := by
    have hp2 : 2^(k+2) = 4 * P := by dsimp [P]; rw [pow_add]; norm_num; ring
    have : 2 * 2^(k+2) ≤ C ∧ C < 3 * 2^(k+2) := by omega
    exact prop_implies_a_eq_0_k (n + 1) (k + 2) ht_1 this.1 this.2
  have hL_ge_2 : L ≥ 2 := by
    by_contra hL
    have : L = 1 := by omega
    subst this
    have : a (n + 1) ≠ 0 := h_after
    exact this ha_1
  have h_run_bounds := run_0_bounds A B C P hk1 hk2 hB_exact.1 hB_exact.2 hC_exact.1 hC_exact.2 hB_bounds.1 hB_bounds.2 hC_bounds.1 hC_bounds.2
  have hT2 : tribonacci (n + 2) = C + B + A := trib_eq_shift n (by omega)
  have hT3 : tribonacci (n + 3) = tribonacci (n + 2) + C + B := trib_eq_shift (n + 1) (by omega)
  have hT4 : tribonacci (n + 4) = tribonacci (n + 3) + tribonacci (n + 2) + C := trib_eq_shift (n + 2) (by omega)
  have hT5 : tribonacci (n + 5) = tribonacci (n + 4) + tribonacci (n + 3) + tribonacci (n + 2) := trib_eq_shift (n + 3) (by omega)
  have h_exp := trib_expand A B C (tribonacci (n + 2)) (tribonacci (n + 3)) (tribonacci (n + 4)) (tribonacci (n + 5)) hT2 hT3 hT4 hT5
  have hT2_eq : tribonacci (n + 2) = A + B + C := h_exp.1
  have hT3_eq : tribonacci (n + 3) = A + 2 * B + 2 * C := h_exp.2.1
  have hT4_eq : tribonacci (n + 4) = 2 * A + 3 * B + 4 * C := h_exp.2.2.1
  have hT5_eq : tribonacci (n + 5) = 4 * A + 6 * B + 7 * C := h_exp.2.2.2
  have ha_2 : a (n + 2) = 0 := by
    have hp3 : 2^(k+3) = 8 * P := by dsimp [P]; rw [pow_add]; norm_num; ring
    have : 2 * 2^(k+3) ≤ tribonacci (n + 2) ∧ tribonacci (n + 2) < 3 * 2^(k+3) := by
      rcases h_run_bounds with ⟨hx2_1, hx2_2, _⟩
      omega
    exact prop_implies_a_eq_0_k (n + 2) (k + 3) ht_2 this.1 this.2
  have hL_ge_3 : L ≥ 3 := by
    by_contra hL
    have : L = 2 := by omega
    subst this
    have : a (n + 2) ≠ 0 := h_after
    exact this ha_2
  have ha_3 : a (n + 3) = 0 := by
    have hp4 : 2^(k+4) = 16 * P := by dsimp [P]; rw [pow_add]; norm_num; ring
    have : 2 * 2^(k+4) ≤ tribonacci (n + 3) ∧ tribonacci (n + 3) < 3 * 2^(k+4) := by
      rcases h_run_bounds with ⟨_, _, hx3_1, hx3_2, _⟩
      omega
    exact prop_implies_a_eq_0_k (n + 3) (k + 4) ht_3 this.1 this.2
  have hL_ge_4 : L ≥ 4 := by
    by_contra hL
    have : L = 3 := by omega
    subst this
    have : a (n + 3) ≠ 0 := h_after
    exact this ha_3
  have h_x4_cases : tribonacci (n + 4) < 64 * P ∨ tribonacci (n + 4) ≥ 64 * P := by omega
  rcases h_x4_cases with h_x4_lt | h_x4_ge
  · have ha_4 : a (n + 4) = 1 := by
      have hp4 : 2^(k+4) = 16 * P := by dsimp [P]; rw [pow_add]; norm_num; ring
      have : 3 * 2^(k+4) ≤ tribonacci (n + 4) ∧ tribonacci (n + 4) < 4 * 2^(k+4) := by
        rcases h_run_bounds with ⟨_, _, _, _, hx4_1, _⟩
        omega
      exact prop_implies_a_eq_1_k (n + 4) (k + 4) ht_4 this.1 this.2
    have hL_eq_4 : L = 4 := by
      by_contra hL
      have : L ≥ 5 := by omega
      have : a (n + 4) = 0 := h_run 4 (by omega)
      omega
    exact Or.inl hL_eq_4
  · have ha_4 : a (n + 4) = 0 := by
      have hp5 : 2^(k+5) = 32 * P := by dsimp [P]; rw [pow_add]; norm_num; ring
      have : 2 * 2^(k+5) ≤ tribonacci (n + 4) ∧ tribonacci (n + 4) < 3 * 2^(k+5) := by
        rcases h_run_bounds with ⟨_, _, _, _, _, hx4_2, _⟩
        omega
      exact prop_implies_a_eq_0_k (n + 4) (k + 5) ht_4 this.1 this.2
    have hL_ge_5 : L ≥ 5 := by
      by_contra hL
      have : L = 4 := by omega
      subst this
      have : a (n + 4) ≠ 0 := h_after
      exact this ha_4
    have ha_5 : a (n + 5) = 1 := by
      have hp5 : 2^(k+5) = 32 * P := by dsimp [P]; rw [pow_add]; norm_num; ring
      have : 3 * 2^(k+5) ≤ tribonacci (n + 5) ∧ tribonacci (n + 5) < 4 * 2^(k+5) := by
        rcases h_run_bounds with ⟨_, _, _, _, _, _, hx5⟩
        have h_ge : 2 * A + 3 * B + 4 * C ≥ 64 * P := by omega
        have hx5_eval := hx5 h_ge
        omega
      exact prop_implies_a_eq_1_k (n + 5) (k + 5) ht_5 this.1 this.2
    have hL_eq_5 : L = 5 := by
      by_contra hL
      have : L ≥ 6 := by omega
      have : a (n + 5) = 0 := h_run 5 (by omega)
      omega
    exact Or.inr hL_eq_5

lemma run_1_main (n L : ℕ) (hn : n ≥ 9) (h : is_maximal_run 1 n L) : L = 3 ∨ L = 4 := by
  rcases h with ⟨hn_ge_2, hL_ge_1, h_run, h_after, h_before⟩
  have ht_m1 : tribonacci (n - 1) > 1 := trib_gt_1 (n - 1) (by omega)
  have ht_0 : tribonacci n > 1 := trib_gt_1 n (by omega)
  have ht_1 : tribonacci (n + 1) > 1 := trib_gt_1 (n + 1) (by omega)
  have ht_2 : tribonacci (n + 2) > 1 := trib_gt_1 (n + 2) (by omega)
  have ht_3 : tribonacci (n + 3) > 1 := trib_gt_1 (n + 3) (by omega)
  have ht_4 : tribonacci (n + 4) > 1 := trib_gt_1 (n + 4) (by omega)
  have ha_m1 : a (n - 1) = 0 := by
    have hd := a_dichotomy (n - 1)
    tauto
  have ha_0 : a n = 1 := h_run 0 (by omega)
  have hk : ∃ k, 2 * 2^k ≤ tribonacci (n - 1) ∧ tribonacci (n - 1) < 3 * 2^k := a_eq_0_prop_k (n - 1) ht_m1 ha_m1
  rcases hk with ⟨k, hk1, hk2⟩
  set P := 2^k
  set A := tribonacci (n - 1)
  set B := tribonacci n
  set C := tribonacci (n + 1)
  have hB_bounds_raw := valid_bounds_all (n - 1) (by omega)
  have hB_bounds : 183 * A ≤ 100 * B ∧ 100 * B ≤ 185 * A := by
    dsimp [valid_bounds] at hB_bounds_raw
    have : n - 1 + 1 = n := by omega
    rw [this] at hB_bounds_raw
    exact hB_bounds_raw
  have hk0_b : B < 6 * P := by omega
  have hk0_a : 3 * P ≤ B := by omega
  have hk_B : ∃ k', 3 * 2^k' ≤ B ∧ B < 4 * 2^k' := a_eq_1_prop_k n ht_0 ha_0
  rcases hk_B with ⟨k', hk'1, hk'2⟩
  have h_k' : k' = k := k_unique_1 k k' B hk0_a hk0_b hk'1 hk'2
  have hB_exact : 3 * P ≤ B ∧ B < 4 * P := by
    subst h_k'
    exact ⟨hk'1, hk'2⟩
  have hC_bounds_raw := valid_bounds_all n (by omega)
  have hC_bounds : 183 * B ≤ 100 * C ∧ 100 * C ≤ 185 * B := by
    dsimp [valid_bounds] at hC_bounds_raw
    exact hC_bounds_raw
  have hC_exact : 6 * P ≤ C ∧ C < 8 * P := run_1_a_n1 A B C P hk1 hk2 hB_exact.1 hB_exact.2 hB_bounds.1 hB_bounds.2 hC_bounds.1 hC_bounds.2
  have ha_1 : a (n + 1) = 1 := by
    have hp1 : 2^(k+1) = 2 * P := by dsimp [P]; rw [pow_add, pow_one, mul_comm]
    have : 3 * 2^(k+1) ≤ C ∧ C < 4 * 2^(k+1) := by omega
    exact prop_implies_a_eq_1_k (n + 1) (k + 1) ht_1 this.1 this.2
  have hL_ge_2 : L ≥ 2 := by
    by_contra hL
    have : L = 1 := by omega
    subst this
    have : a (n + 1) ≠ 1 := h_after
    exact this ha_1
  have h_run_bounds := run_1_bounds A B C P hk1 hk2 hB_exact.1 hB_exact.2 hC_exact.1 hC_exact.2 hB_bounds.1 hB_bounds.2 hC_bounds.1 hC_bounds.2
  have hT2 : tribonacci (n + 2) = C + B + A := trib_eq_shift n (by omega)
  have hT3 : tribonacci (n + 3) = tribonacci (n + 2) + C + B := trib_eq_shift (n + 1) (by omega)
  have hT4 : tribonacci (n + 4) = tribonacci (n + 3) + tribonacci (n + 2) + C := trib_eq_shift (n + 2) (by omega)
  have hT2_eq : tribonacci (n + 2) = A + B + C := by omega
  have hT3_eq : tribonacci (n + 3) = A + 2 * B + 2 * C := by omega
  have hT4_eq : tribonacci (n + 4) = 2 * A + 3 * B + 4 * C := by omega
  have ha_2 : a (n + 2) = 1 := by
    have hp2 : 2^(k+2) = 4 * P := by dsimp [P]; rw [pow_add]; norm_num; ring
    have : 3 * 2^(k+2) ≤ tribonacci (n + 2) ∧ tribonacci (n + 2) < 4 * 2^(k+2) := by
      rcases h_run_bounds with ⟨hx2_1, hx2_2, _⟩
      omega
    exact prop_implies_a_eq_1_k (n + 2) (k + 2) ht_2 this.1 this.2
  have hL_ge_3 : L ≥ 3 := by
    by_contra hL
    have : L = 2 := by omega
    subst this
    have : a (n + 2) ≠ 1 := h_after
    exact this ha_2
  have h_x3_cases : tribonacci (n + 3) < 24 * P ∨ tribonacci (n + 3) ≥ 24 * P := by omega
  rcases h_x3_cases with h_x3_lt | h_x3_ge
  · have ha_3 : a (n + 3) = 0 := by
      have hp3 : 2^(k+3) = 8 * P := by dsimp [P]; rw [pow_add]; norm_num; ring
      have : 2 * 2^(k+3) ≤ tribonacci (n + 3) ∧ tribonacci (n + 3) < 3 * 2^(k+3) := by
        rcases h_run_bounds with ⟨_, _, hx3_1, _, _⟩
        omega
      exact prop_implies_a_eq_0_k (n + 3) (k + 3) ht_3 this.1 this.2
    have hL_eq_3 : L = 3 := by
      by_contra hL
      have : L ≥ 4 := by omega
      have : a (n + 3) = 1 := h_run 3 (by omega)
      omega
    exact Or.inl hL_eq_3
  · have ha_3 : a (n + 3) = 1 := by
      have hp3 : 2^(k+3) = 8 * P := by dsimp [P]; rw [pow_add]; norm_num; ring
      have : 3 * 2^(k+3) ≤ tribonacci (n + 3) ∧ tribonacci (n + 3) < 4 * 2^(k+3) := by
        rcases h_run_bounds with ⟨_, _, _, hx3_2, _⟩
        omega
      exact prop_implies_a_eq_1_k (n + 3) (k + 3) ht_3 this.1 this.2
    have hL_ge_4 : L ≥ 4 := by
      by_contra hL
      have : L = 3 := by omega
      subst this
      have : a (n + 3) ≠ 1 := h_after
      exact this ha_3
    have ha_4 : a (n + 4) = 0 := by
      have hp4 : 2^(k+4) = 16 * P := by dsimp [P]; rw [pow_add]; norm_num; ring
      have : 2 * 2^(k+4) ≤ tribonacci (n + 4) ∧ tribonacci (n + 4) < 3 * 2^(k+4) := by
        rcases h_run_bounds with ⟨_, _, _, _, hx4⟩
        have h_ge : A + 2 * B + 2 * C ≥ 24 * P := by omega
        have hx4_eval := hx4 h_ge
        omega
      exact prop_implies_a_eq_0_k (n + 4) (k + 4) ht_4 this.1 this.2
    have hL_eq_4 : L = 4 := by
      by_contra hL
      have : L ≥ 5 := by omega
      have : a (n + 4) = 1 := h_run 4 (by omega)
      omega
    exact Or.inr hL_eq_4
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : (∀ n L, is_maximal_run 0 n L → (L = 4 ∨ L = 5)) ∧ (∀ n L, is_maximal_run 1 n L → (L = 3 ∨ L = 4)) := by
  -- EVOLVE-BLOCK-START
  have h0 : ∀ n L, is_maximal_run 0 n L → (L = 4 ∨ L = 5) := by
    intros n L h
    rcases lt_trichotomy n 9 with hn | hn | hn
    · exfalso
      exact small_cases_0 n L hn h
    · exact run_0_main n L (by omega) h
    · exact run_0_main n L (by omega) h
  have h1 : ∀ n L, is_maximal_run 1 n L → (L = 3 ∨ L = 4) := by
    intros n L h
    rcases lt_trichotomy n 9 with hn | hn | hn
    · exact small_cases_1 n L hn h
    · exact run_1_main n L (by omega) h
    · exact run_1_main n L (by omega) h
  exact ⟨h0, h1⟩
  -- EVOLVE-BLOCK-END
