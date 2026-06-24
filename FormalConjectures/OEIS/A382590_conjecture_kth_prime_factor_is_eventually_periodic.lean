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




open Int

/--
Helper function for A382590, computing the pair $(a(n), b(n))$ such that:
$a(n) = a(n-1)b(n-2) + a(n-2)b(n-1)$
$b(n) = a(n-1)b(n-2) - a(n-2)b(n-1)$
-/
def A382590_pair : ℕ → ℤ × ℤ
| 0 => (1, 1)
| 1 => (2, 1)
| n + 2 =>
  let (a_n_plus_1, b_n_plus_1) := A382590_pair (n + 1)
  let (a_n, b_n) := A382590_pair n
  (a_n_plus_1 * b_n + a_n * b_n_plus_1, a_n_plus_1 * b_n - a_n * b_n_plus_1)

/--
A382590: $a(n)$ is the sequence defined by the mutual recurrence relations:
$a(n) = a(n-1)b(n-2) + a(n-2)b(n-1)$ and $b(n) = a(n-1)b(n-2) - a(n-2)b(n-1)$
starting with $a(0) = b(0) = b(1) = 1$ and a(1) = 2.
The terms are in $\mathbb{Z}$ due to negative values.
-/
def A382590 (n : ℕ) : ℤ := (A382590_pair n).fst

open Nat

/--
The k-th prime factor of an integer n (where k>=1), counted with multiplicity.
This is defined as the k-th element (0-indexed k-1) of `Nat.primeFactorsList n.natAbs`.
Returns 1 if n has fewer than k prime factors or if n is 0, 1, or -1, following the informal convention.
-/
def kth_prime_factor (k : ℕ) (n : ℤ) : ℕ :=
  if h₀ : k = 0 then 1 else
  let n_abs := Int.natAbs n
  let L := primeFactorsList n_abs
  -- prime factors list length is L.length. We look for k-th element, index k-1.
  if h_len : k - 1 ≥ L.length then 1 else
  L[k - 1]

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

def next_state (s : (ℤ × ℤ) × (ℤ × ℤ)) : (ℤ × ℤ) × (ℤ × ℤ) :=
  (s.2, ((s.2.1 * s.1.2 + s.1.1 * s.2.2) % 15, (s.2.1 * s.1.2 - s.1.1 * s.2.2) % 15))

def state_seq : ℕ → (ℤ × ℤ) × (ℤ × ℤ)
| 0 => ((1, 1), (2, 1))
| n + 1 => next_state (state_seq n)

lemma A382590_mod_15 (n : ℕ) :
  (A382590_pair n).1 % 15 = (state_seq n).1.1 ∧
  (A382590_pair n).2 % 15 = (state_seq n).1.2 ∧
  (A382590_pair (n + 1)).1 % 15 = (state_seq n).2.1 ∧
  (A382590_pair (n + 1)).2 % 15 = (state_seq n).2.2 := by
  refine(n).strongRec fun and(a) =>match and with|0|1|2=>by decide | S+3 =>?_
  norm_num[state_seq, A382590_pair,<-a]
  norm_num[next_state,←a,Int.add_emod,Int.sub_emod,Int.mul_emod]at*

def valid_states : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [ ((1, 1), (2, 1)),
    ((2, 1), (3, 1)),
    ((3, 1), (5, 1)),
    ((5, 1), (8, 2)),
    ((8, 2), (3, 13)),
    ((3, 13), (5, 7)),
    ((5, 7), (11, 14)),
    ((11, 14), (12, 7)),
    ((12, 7), (5, 1)),
    ((5, 1), (2, 8)),
    ((2, 8), (12, 7)),
    ((12, 7), (5, 7)),
    ((5, 7), (14, 11)),
    ((14, 11), (3, 13)),
    ((3, 13), (5, 1)) ]

lemma state_seq_in_valid (n : ℕ) : state_seq n ∈ valid_states := by
  norm_num[state_seq, false,valid_states]
  use n.strongRec ?_
  rintro(x | S | S) and
  · iterate constructor
  · trivial
  rcases and S (by valid) with S | S | S | S | S | S | S | S | S | S | S | S | S | S | S
  · simp_all!
    tauto
  · simp_all!
    tauto
  · simp_all!
    tauto
  · simp_all!
    tauto
  · simp_all!
    tauto
  · simp_all![Nat.forall_lt_succ]
    tauto
  · simp_all!
    tauto
  · simp_all![Nat.forall_lt_succ]
    norm_num[next_state]
  · simp_all!
    norm_num[next_state]
  · simp_all!
    norm_num[next_state]
  · simp_all![Nat.forall_lt_succ]
    norm_num[next_state]
  · simp_all!
    norm_num[next_state]
  · simp_all![Nat.forall_lt_succ]
    simp_all[next_state]
  · simp_all!
    tauto
  · simp_all!
    simp_all![next_state]

lemma state_seq_fst_not_zero (s : ((ℤ × ℤ) × (ℤ × ℤ))) (h : s ∈ valid_states) : s.1.1 ≠ 0 := by
  delta valid_states at h
  classical decide+revert

lemma a_n_not_zero (n : ℕ) : (A382590_pair n).1 ≠ 0 := by
  intro h
  have h1 := (A382590_mod_15 n).1
  rw [h] at h1
  have h_zero : (0 : ℤ) % 15 = 0 := rfl
  rw [h_zero] at h1
  have h2 := state_seq_in_valid n
  have h3 := state_seq_fst_not_zero (state_seq n) h2
  exact h3 h1.symm

def u_seq : ℕ → ℕ
| 0 => 0
| 1 => 0
| 2 => 0
| 3 => 0
| 4 => 1
| 5 => 1
| n + 6 => u_seq (n + 5) + u_seq (n + 4)

lemma div_by_u_seq_step (u1 u2 : ℕ) (a1 b1 a2 b2 : ℤ)
  (h1a : (2^u1 : ℤ) ∣ a1) (h1b : (2^u1 : ℤ) ∣ b1)
  (h2a : (2^u2 : ℤ) ∣ a2) (h2b : (2^u2 : ℤ) ∣ b2) :
  (2^(u1 + u2) : ℤ) ∣ a1 * b2 + a2 * b1 ∧
  (2^(u1 + u2) : ℤ) ∣ a1 * b2 - a2 * b1 := by
  have h3 : (2^(u1 + u2) : ℤ) ∣ a1 * b2 := by
    rw [pow_add]
    exact mul_dvd_mul h1a h2b
  have h4 : (2^(u1 + u2) : ℤ) ∣ a2 * b1 := by
    rw [add_comm u1 u2, pow_add]
    exact mul_dvd_mul h2a h1b
  constructor
  · exact dvd_add h3 h4
  · exact dvd_sub h3 h4

lemma div_by_u_seq (n : ℕ) : (2 ^ u_seq n : ℤ) ∣ (A382590_pair n).1 ∧ (2 ^ u_seq n : ℤ) ∣ (A382590_pair n).2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | _ | _ | m
    · norm_num [u_seq, A382590_pair]
    · norm_num [u_seq, A382590_pair]
    · norm_num [u_seq, A382590_pair]
    · norm_num [u_seq, A382590_pair]
    · norm_num [u_seq, A382590_pair]
    · norm_num [u_seq, A382590_pair]
    · have ih1 := ih (m + 5) (by omega)
      have ih2 := ih (m + 4) (by omega)
      have h_step := div_by_u_seq_step (u_seq (m + 5)) (u_seq (m + 4))
        (A382590_pair (m + 5)).1 (A382590_pair (m + 5)).2
        (A382590_pair (m + 4)).1 (A382590_pair (m + 4)).2
        ih1.1 ih1.2 ih2.1 ih2.2
      have hu : u_seq (m + 6) = u_seq (m + 5) + u_seq (m + 4) := rfl
      have ha : (A382590_pair (m + 6)) =
        let (a1, b1) := A382590_pair (m + 5)
        let (a2, b2) := A382590_pair (m + 4)
        (a1 * b2 + a2 * b1, a1 * b2 - a2 * b1) := rfl
      rw [hu, ha]
      exact h_step

lemma u_seq_bound (n : ℕ) : n ≥ 4 → u_seq n ≥ n - 4 := by
  use fun and=>n.sub_add_cancel and▸(n-4).strongRec fun and p=>match and with|0|1=>by decide | S+2=>?_
  simp_all![Nat.succ_le,Nat.forall_lt_succ]
  cases S with|zero=>simp_all![u_seq]|succ=>exact (Nat.add_le_add p.2 (Nat.one_le_of_lt (p.1 _ (by constructor))))

lemma a_n_div_2_pow (n k : ℕ) (hn : n ≥ k + 4) : (2 ^ k : ℤ) ∣ (A382590_pair n).1 := by
  have h1 := u_seq_bound n (by omega)
  have h2 := div_by_u_seq n
  have h3 : k ≤ u_seq n := by omega
  have h4 : (2 ^ k : ℤ) ∣ 2 ^ u_seq n := by exact pow_dvd_pow 2 h3
  exact dvd_trans h4 h2.1

lemma padicValNat_two_ge (N k : ℕ) (hN : N ≠ 0) (hdvd : 2 ^ k ∣ N) : padicValNat 2 N ≥ k := by
  refine(padicValNat_dvd_iff_le hN).mp hdvd

lemma count_two_primeFactorsList (N : ℕ) (hN : N ≠ 0) :
  (Nat.primeFactorsList N).count 2 = padicValNat 2 N := by
  norm_num[ N.factorization_def]

lemma sorted_primeFactorsList_ge_two {N : ℕ} (hN : N ≠ 0) (p : ℕ) (hp : p ∈ Nat.primeFactorsList N) : p ≥ 2 := by
  have h_prime : p.Prime := Nat.prime_of_mem_primeFactorsList hp
  exact Nat.Prime.two_le h_prime

lemma get_eq_two_of_count_ge (N : ℕ)
  (h_min : ∀ x ∈ Nat.primeFactorsList N, x ≥ 2) (m : ℕ) (hm : m < (Nat.primeFactorsList N).count 2) (h_len : m < (Nat.primeFactorsList N).length) :
  (Nat.primeFactorsList N)[m] = 2 := by
  have h_sorted := Nat.primeFactorsList_sorted N
  have' := N.primeFactorsList.sum_toFinset_count_eq_length
  use le_antisymm (not_lt.1 fun and=>hm.not_ge ?_) (h_min _ (by norm_num))
  trans{ a ∈ Finset.range N.primeFactorsList.length| N.primeFactorsList.getI a=2}.card
  · exact (ge_of_eq (( Finset.card_filter _ _).trans ( N.primeFactorsList.rec rfl fun and A B=>.trans ( Finset.sum_range_succ' _ _) (B▸by norm_num[List.count_cons,List.getI]))))
  · use Finset.card_range m▸ Finset.card_mono fun a s=>List.mem_range.2 (not_le.1 (and.not_ge ∘(( Finset.mem_filter.1 s).2▸List.getI_eq_getElem _ (List.mem_range.1 (Finset.filter_subset _ _ s))▸by tauto)))

lemma kth_prime_factor_eq_2 (k : ℕ) (n : ℤ) (hk : k ≥ 2) (hn : n ≠ 0) (hdvd : (2 ^ k : ℤ) ∣ n) :
  kth_prime_factor k n = 2 := by
  have hn_abs : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  have hdvd_nat : 2 ^ k ∣ n.natAbs := by
    exact_mod_cast n.natCast_dvd.mp hdvd
  have h_padic := padicValNat_two_ge n.natAbs k hn_abs hdvd_nat
  have h_count := count_two_primeFactorsList n.natAbs hn_abs
  have h_count_ge : k ≤ (Nat.primeFactorsList n.natAbs).count 2 := by omega
  have h_len : k - 1 < (Nat.primeFactorsList n.natAbs).length := by
    have h3 : (Nat.primeFactorsList n.natAbs).count 2 ≤ (Nat.primeFactorsList n.natAbs).length := List.count_le_length
    omega
  unfold kth_prime_factor
  have hk0 : k ≠ 0 := by omega
  rw [dif_neg hk0]
  dsimp
  have hlen_not : ¬ (k - 1 ≥ (Nat.primeFactorsList n.natAbs).length) := by omega
  rw [dif_neg hlen_not]
  have h_min : ∀ x ∈ Nat.primeFactorsList n.natAbs, x ≥ 2 := sorted_primeFactorsList_ge_two hn_abs
  exact get_eq_two_of_count_ge n.natAbs h_min (k - 1) (by omega) (by omega)

-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : ∀ k : ℕ, k ≥ 2 → ∃ N₀ p : ℕ, p > 0 ∧ ∀ n : ℕ, n ≥ N₀ → kth_prime_factor k (A382590 (n + p)) = kth_prime_factor k (A382590 n) := by
  -- EVOLVE-BLOCK-START
  intros k hk
  use k + 4, 1
  refine ⟨by omega, ?_⟩
  intros n hn
  have hn1 : n + 1 ≥ k + 4 := by omega
  have hn_ge : n ≥ k + 4 := by omega
  have ha1_div := a_n_div_2_pow (n + 1) k hn1
  have ha_div := a_n_div_2_pow n k hn_ge
  have ha1_nz := a_n_not_zero (n + 1)
  have ha_nz := a_n_not_zero n
  have h1 : kth_prime_factor k (A382590 (n + 1)) = 2 := by
    exact kth_prime_factor_eq_2 k (A382590 (n + 1)) hk ha1_nz ha1_div
  have h2 : kth_prime_factor k (A382590 n) = 2 := by
    exact kth_prime_factor_eq_2 k (A382590 n) hk ha_nz ha_div
  rw [h1, h2]
  -- EVOLVE-BLOCK-END
