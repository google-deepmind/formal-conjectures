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




/--
A248802: Smallest prime factor of $2^{(2^n+2)} + 3$.
-/
def a (n : ℕ) : ℕ := (2 ^ (2 ^ n + 2) + 3).minFac

/-- An index k is covered by Conjecture 1 if k = 10m + 2 for some m >= 0, predicting a(k)=67. -/
def covered_by_C1 (k : ℕ) : Prop := ∃ m : ℕ, k = 10 * m + 2

/-- An index k is covered by Conjecture 2 if k = 36m + 16 for some m >= 0, and m is not 1 mod 5, predicting a(k)=271. -/
def covered_by_C2 (k : ℕ) : Prop := ∃ m : ℕ, k = 36 * m + 16 ∧ m % 5 ≠ 1

/-- An index k is covered by Conjecture 3 if k = 84m + 22 for some m >= 0, and m is not 0 mod 5, predicting a(k)=523. -/
def covered_by_C3 (k : ℕ) : Prop := ∃ m : ℕ, k = 84 * m + 22 ∧ m % 5 ≠ 0

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
lemma mod_1399_step1 : 2^58 ≡ 1 [MOD 233] := by decide

lemma mod_1399_step2 (n : ℕ) : (2^58)^n ≡ 1 [MOD 233] := by
  have h := Nat.ModEq.pow n mod_1399_step1
  rw [one_pow] at h
  exact h

lemma mod_1399_step3 (n : ℕ) : 2^(58 * n + 26) ≡ 204 [MOD 233] := by
  have h1 : 2^(58 * n + 26) = (2^58)^n * 2^26 := by
    rw [pow_add, pow_mul]
  rw [h1]
  have h2 : (2^58)^n * 2^26 ≡ 1 * 2^26 [MOD 233] :=
    Nat.ModEq.mul_right (2^26) (mod_1399_step2 n)
  have h3 : 1 * 2^26 ≡ 204 [MOD 233] := by decide
  exact Nat.ModEq.trans h2 h3

lemma mod_1399_step4 : 2^233 ≡ 1 [MOD 1399] := by decide

lemma exp_ge_204 (n : ℕ) : 204 ≤ 2^(58 * n + 26) := by
  calc 204 ≤ 2^26 := by decide
       _ ≤ 2^(58 * n + 26) := Nat.pow_le_pow_right (by decide) (Nat.le_add_left 26 (58 * n))

lemma modEq_to_eq (X c m : ℕ) (h1 : X ≡ c [MOD m]) (h2 : c ≤ X) (h3 : c < m) : ∃ k, X = m * k + c := by
  use X / m
  have h_mod : X % m = c % m := h1
  have h_c : c % m = c := Nat.mod_eq_of_lt h3
  rw [h_c] at h_mod
  have h_div := Nat.div_add_mod X m
  rw [h_mod] at h_div
  exact h_div.symm

lemma mod_1399_step5 (n : ℕ) : 2^(2^(58 * n + 26)) ≡ 349 [MOD 1399] := by
  have h_eq := modEq_to_eq (2^(58 * n + 26)) 204 233 (mod_1399_step3 n) (exp_ge_204 n) (by decide)
  rcases h_eq with ⟨k, hk⟩
  rw [hk]
  have h1 : 2^(233 * k + 204) = (2^233)^k * 2^204 := by
    rw [pow_add, pow_mul]
  rw [h1]
  have h2 : (2^233)^k ≡ 1^k [MOD 1399] := Nat.ModEq.pow k mod_1399_step4
  rw [one_pow] at h2
  have h3 : (2^233)^k * 2^204 ≡ 1 * 2^204 [MOD 1399] := Nat.ModEq.mul_right (2^204) h2
  have h4 : 1 * 2^204 ≡ 349 [MOD 1399] := by decide
  exact Nat.ModEq.trans h3 h4

lemma mod_1399_step6 (n : ℕ) : 2^(2^(58 * n + 26) + 2) + 3 ≡ 0 [MOD 1399] := by
  have h1 : 2^(2^(58 * n + 26) + 2) + 3 = 2^(2^(58 * n + 26)) * 2^2 + 3 := by
    rw [pow_add]
  rw [h1]
  have h2 : 2^(2^(58 * n + 26)) * 2^2 ≡ 349 * 4 [MOD 1399] := by
    have ht := Nat.ModEq.mul_right (2^2) (mod_1399_step5 n)
    exact ht
  have h3 : 2^(2^(58 * n + 26)) * 2^2 + 3 ≡ 349 * 4 + 3 [MOD 1399] :=
    Nat.ModEq.add_right 3 h2
  have h4 : 349 * 4 + 3 ≡ 0 [MOD 1399] := by decide
  exact Nat.ModEq.trans h3 h4

lemma divides_1399 (n : ℕ) : 1399 ∣ 2^(2^(58 * n + 26) + 2) + 3 := by
  have h := mod_1399_step6 n
  exact Nat.dvd_of_mod_eq_zero h

def pow_mod (a b m : ℕ) : ℕ := Id.run do
  let mut res := 1
  let mut base := a % m
  let mut exp := b
  while exp > 0 do
    if exp % 2 == 1 then res := (res * base) % m
    base := (base * base) % m
    exp := exp / 2
  return res

def is_prime (p : ℕ) : Bool := Id.run do
  if p < 2 then return false
  for i in [2:p] do
    if p % i == 0 then return false
  return true

def bad_for_even_k (p : ℕ) : Bool := Id.run do
  if p == 2 then return false
  let mut x := 1
  for _ in [1:p+1] do
    x := (x * 4) % (p - 1)
    let val := (pow_mod 2 (x + 2) p + 3) % p
    if val == 0 then return true
  return false

#eval! (List.range 1399).filter is_prime |>.filter bad_for_even_k



lemma zmod_pow_mod (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p > 2) (k : ℕ) :
  (2 : ZMod p) ^ k = (2 : ZMod p) ^ (k % (p - 1)) := by
  exact (pow_eq_pow_mod _) (ZMod.pow_card_sub_one_eq_one (by cases p.eq_zero_of_dvd_of_lt.comp (CharP.cast_eq_zero_iff _ _ _).mp · hp2))

lemma not_C1_implies (k : ℕ) (h : ¬ covered_by_C1 k) : k % 10 ≠ 2 := by
  intro hk
  apply h
  use k / 10
  have h_div := Nat.div_add_mod k 10
  rw [hk] at h_div
  exact h_div.symm

lemma not_C1_C2_implies (k : ℕ) (h1 : ¬ covered_by_C1 k) (h2 : ¬ covered_by_C2 k) : k % 36 ≠ 16 := by
  intro hk
  have h_div := Nat.div_add_mod k 36
  rw [hk] at h_div
  let m := k / 36
  have hk_eq : k = 36 * m + 16 := h_div.symm
  by_cases hm : m % 5 = 1
  · apply h1
    use 18 * (m / 5) + 5
    have h_m_div := Nat.div_add_mod m 5
    rw [hm] at h_m_div
    have hm_eq : m = 5 * (m / 5) + 1 := h_m_div.symm
    rw [hm_eq] at hk_eq
    linarith
  · apply h2
    use m

lemma not_C1_C3_implies (k : ℕ) (h1 : ¬ covered_by_C1 k) (h3 : ¬ covered_by_C3 k) : k % 84 ≠ 22 := by
  intro hk
  have h_div := Nat.div_add_mod k 84
  rw [hk] at h_div
  let m := k / 84
  have hk_eq : k = 84 * m + 22 := h_div.symm
  by_cases hm : m % 5 = 0
  · apply h1
    use 42 * (m / 5) + 2
    have h_m_div := Nat.div_add_mod m 5
    rw [hm] at h_m_div
    have hm_eq : m = 5 * (m / 5) := by linarith
    rw [hm_eq] at hk_eq
    linarith
  · apply h3
    use m

lemma p_mod_base (P mod k0 : ℕ) (k : ℕ) (hk : k ≥ k0) (h_base : 2^(k0 + P) ≡ 2^k0 [MOD mod]) : 2^(k + P) ≡ 2^k [MOD mod] := by
  have h1 : 2^(k + P) = 2^(k - k0) * 2^(k0 + P) := by
    rw [← pow_add]
    have h_eq : k - k0 + (k0 + P) = k + P := by omega
    rw [h_eq]
  have h2 : 2^k = 2^(k - k0) * 2^k0 := by
    rw [← pow_add]
    have h_eq : k - k0 + k0 = k := by omega
    rw [h_eq]
  rw [h1, h2]
  exact Nat.ModEq.mul_left (2^(k - k0)) h_base

lemma p_67_mod (k : ℕ) (hk : k ≥ 1) : 2^(k+10) ≡ 2^k [MOD 66] := by
  apply p_mod_base 10 66 1 k hk (by decide)

lemma p_271_mod (k : ℕ) (hk : k ≥ 2) : 2^(k+36) ≡ 2^k [MOD 270] := by
  apply p_mod_base 36 270 2 k hk (by decide)

lemma p_523_mod (k : ℕ) (hk : k ≥ 2) : 2^(k+84) ≡ 2^k [MOD 522] := by
  apply p_mod_base 84 522 2 k hk (by decide)

lemma period_mod_ind (P mod k0 : ℕ) (hP : P ≥ k0) (h_per : ∀ k ≥ k0, 2^(k+P) ≡ 2^k [MOD mod]) (r j : ℕ) :
  2^(r + (j + 1) * P) ≡ 2^(r + P) [MOD mod] := by
  induction j with
  | zero =>
    have h1 : r + (0 + 1) * P = r + P := by ring
    rw [h1]
  | succ j ih =>
    have h1 : r + (j + 1 + 1) * P = r + (j + 1) * P + P := by ring
    rw [h1]
    have hp : 2^(r + (j + 1) * P + P) ≡ 2^(r + (j + 1) * P) [MOD mod] := by
      apply h_per
      have h_pos : (j + 1) * P ≥ 1 * P := Nat.mul_le_mul_right P (by omega)
      have h_pos2 : 1 * P = P := by ring
      rw [h_pos2] at h_pos
      omega
    exact Nat.ModEq.trans hp ih

lemma p_mod_all_generic (P mod k0 : ℕ) (hP : P ≥ k0) (hP_pos : P > 0) (h_per : ∀ k ≥ k0, 2^(k+P) ≡ 2^k [MOD mod]) (k : ℕ) (hk : k ≥ k0) :
  2^k ≡ 2^(k % P + P) [MOD mod] := by
  by_cases h_lt : k < P
  · have h_mod_eq : k % P = k := Nat.mod_eq_of_lt h_lt
    rw [h_mod_eq]
    exact (h_per k hk).symm
  · have h_ge : k ≥ P := by omega
    have h_div : k = k % P + P * (k / P) := (Nat.mod_add_div k P).symm
    nth_rw 1 [h_div]
    have hz : k / P = (k / P - 1) + 1 := by
      have h1 : k / P ≥ 1 := Nat.div_pos h_ge hP_pos
      omega
    have ht : k % P + P * (k / P) = k % P + (k / P - 1 + 1) * P := by
      rw [mul_comm P (k / P)]
      nth_rw 1 [hz]
    rw [ht]
    exact period_mod_ind P mod k0 hP h_per (k % P) (k / P - 1)


lemma p_271_mod_all (k : ℕ) (hk : k ≥ 26) : 2^k ≡ 2^(k % 36 + 36) [MOD 270] := by
  apply p_mod_all_generic 36 270 2 (by decide) (by decide) p_271_mod k (by omega)

lemma p_523_mod_all (k : ℕ) (hk : k ≥ 26) : 2^k ≡ 2^(k % 84 + 84) [MOD 522] := by
  apply p_mod_all_generic 84 522 2 (by decide) (by decide) p_523_mod k (by omega)

lemma p_not_div_67 (k : ℕ) (hk1 : k ≥ 26) (hk2 : k % 10 ≠ 2) (h_even : k % 2 = 0) : ¬ 67 ∣ 2^(2^k+2)+3 := by
  rw [← (2 ^k+2 :).mod_add_div @66]
  norm_num[pow_add,pow_mul,k.mod_add_div 10▸pow_add _ _ _,Nat.add_mod,Nat.mul_mod,Nat.pow_mod,Nat.dvd_iff_mod_eq_zero, true, *] at*
  norm_num[Nat.sub_add_cancel (by valid: 1 ≤k/10)▸pow_succ' 34 _,Nat.mul_mod]
  norm_num[ (by induction. with omega : ∀x,34*34^x%66=34)]
  match R:k%10 with|0|1|2|3|4|5|6|7|8|9=>simp_all|n+10=>omega


def sq_mod (p x : ℕ) : ℕ → ℕ
| 0 => x % p
| k + 1 => sq_mod p ((x * x) % p) k

lemma sq_mod_eq (p x k : ℕ) : sq_mod p x k = (x ^ (2^k)) % p := by
  induction k generalizing x with
  | zero => simp [sq_mod]
  | succ k ih =>
    simp [sq_mod, ih]
    have h1 : (((x * x) % p) ^ 2^k) % p = ((x * x) ^ 2^k) % p := by
      exact Nat.ModEq.pow (2^k) (Nat.mod_modEq (x * x) p)
    rw [h1]
    have hs : x * x = x ^ 2 := (pow_two x).symm
    rw [hs, ← pow_mul]
    have hk : 2 * 2^k = 2^(k + 1) := by rw [pow_succ', mul_comm]
    rw [hk]

lemma sq_mod_add (p x A B : ℕ) : sq_mod p x (A + B) = sq_mod p (sq_mod p x A) B := by
  rw [sq_mod_eq, sq_mod_eq, sq_mod_eq]
  have h1 : (((x ^ 2^A) % p) ^ 2^B) % p = ((x ^ 2^A) ^ 2^B) % p := by
    exact Nat.ModEq.pow (2^B) (Nat.mod_modEq (x ^ 2^A) p)
  rw [h1, ← pow_mul, ← pow_add]

def bad_for_k (p : ℕ) (k : ℕ) : Bool :=
  (sq_mod p 2 k * 4 + 3) % p == 0

def check_271_all : Bool :=
  (List.range 36).all (fun r =>
    if r % 2 == 1 || r == 16 then true
    else bad_for_k 271 (r + 36) == false
  )

def check_523_all : Bool :=
  (List.range 84).all (fun r =>
    if r % 2 == 1 || r == 22 then true
    else bad_for_k 523 (r + 84) == false
  )

lemma bad_for_k_iff (p k : ℕ) : bad_for_k p k = true ↔ p ∣ 2^(2^k+2)+3 := by
  unfold bad_for_k
  rw [sq_mod_eq, beq_iff_eq]
  have h1 : 2^(2^k+2) + 3 = 2^(2^k) * 4 + 3 := by
    have h_add : 2^(2^k+2) = 2^(2^k) * 2^2 := pow_add 2 (2^k) 2
    rw [h_add]
    rfl
  rw [h1]
  have h2 : (2^(2^k) * 4 + 3) % p = ((2^(2^k) % p) * 4 + 3) % p := by
    have hm1 : 2^(2^k) * 4 ≡ (2^(2^k) % p) * 4 [MOD p] := Nat.ModEq.mul_right 4 (Nat.mod_modEq (2^(2^k)) p).symm
    have hm2 : 2^(2^k) * 4 + 3 ≡ (2^(2^k) % p) * 4 + 3 [MOD p] := Nat.ModEq.add_right 3 hm1
    exact hm2
  rw [← h2]
  exact Nat.dvd_iff_mod_eq_zero.symm

lemma bad_for_k_periodic (p A B : ℕ) [Fact (Nat.Prime p)] (hp2 : p > 2) (h_eq : 2^A ≡ 2^B [MOD (p - 1)]) :
  bad_for_k p A = bad_for_k p B := by
  unfold bad_for_k
  rw [sq_mod_eq, sq_mod_eq]
  have hA : (2 : ZMod p)^(2^A) = (2 : ZMod p)^(2^B) := by
    have hzA : (2 : ZMod p)^(2^A) = (2 : ZMod p)^(2^A % (p - 1)) := zmod_pow_mod p hp2 (2^A)
    have hzB : (2 : ZMod p)^(2^B) = (2 : ZMod p)^(2^B % (p - 1)) := zmod_pow_mod p hp2 (2^B)
    have h_mod : 2^A % (p - 1) = 2^B % (p - 1) := h_eq
    rw [hzA, hzB, h_mod]
  have hz : (2^(2^A) % p : ℕ) = (2^(2^B) % p : ℕ) := by
    calc 2^(2^A) % p = ZMod.val ((2^(2^A) : ℕ) : ZMod p) := (ZMod.val_natCast p (2^(2^A))).symm
    _ = ZMod.val ((2 : ZMod p)^(2^A)) := by push_cast; rfl
    _ = ZMod.val ((2 : ZMod p)^(2^B)) := by rw [hA]
    _ = ZMod.val ((2^(2^B) : ℕ) : ZMod p) := by push_cast; rfl
    _ = 2^(2^B) % p := ZMod.val_natCast p (2^(2^B))
  rw [hz]

lemma check_271_all_eq : check_271_all = true := by decide

set_option maxRecDepth 10000 in
lemma check_523_all_eq : check_523_all = true := by decide

lemma p_not_div_271 (k : ℕ) (hk1 : k ≥ 26) (hk2 : k % 36 ≠ 16) (h_even : k % 2 = 0) : ¬ 271 ∣ 2^(2^k+2)+3 := by
  intro h_div
  have h_bad : bad_for_k 271 k = true := (bad_for_k_iff 271 k).mpr h_div
  have h_per : bad_for_k 271 k = bad_for_k 271 (k % 36 + 36) := by
    have h_fact : Fact (Nat.Prime 271) := ⟨by norm_num⟩
    exact bad_for_k_periodic 271 k (k % 36 + 36) (by decide) (p_271_mod_all k hk1)
  rw [h_per] at h_bad
  have h_check := check_271_all_eq
  unfold check_271_all at h_check
  have h_in : k % 36 ∈ List.range 36 := List.mem_range.mpr (Nat.mod_lt k (by decide))
  have h_eval := List.all_eq_true.mp h_check (k % 36) h_in
  have h_cond : (k % 36 % 2 == 1 || k % 36 == 16) = false := by
    have h_mod_2 : k % 36 % 2 = 0 := by
      have h_div : k = 36 * (k / 36) + k % 36 := (Nat.div_add_mod k 36).symm
      have hk2_even : k % 2 = 0 := h_even
      omega
    have h_neq : (k % 36 == 16) = false := by
      exact beq_false_of_ne hk2
    have h_mod_2_b : (k % 36 % 2 == 1) = false := by
      rw [h_mod_2]
      rfl
    rw [h_neq, h_mod_2_b]
    rfl
  rw [h_cond] at h_eval
  simp at h_eval
  rw [h_eval] at h_bad
  exact Bool.noConfusion h_bad

lemma p_not_div_523 (k : ℕ) (hk1 : k ≥ 26) (hk2 : k % 84 ≠ 22) (h_even : k % 2 = 0) : ¬ 523 ∣ 2^(2^k+2)+3 := by
  intro h_div
  have h_bad : bad_for_k 523 k = true := (bad_for_k_iff 523 k).mpr h_div
  have h_per : bad_for_k 523 k = bad_for_k 523 (k % 84 + 84) := by
    have h_fact : Fact (Nat.Prime 523) := ⟨by norm_num⟩
    exact bad_for_k_periodic 523 k (k % 84 + 84) (by decide) (p_523_mod_all k hk1)
  rw [h_per] at h_bad
  have h_check := check_523_all_eq
  unfold check_523_all at h_check
  have h_in : k % 84 ∈ List.range 84 := List.mem_range.mpr (Nat.mod_lt k (by decide))
  have h_eval := List.all_eq_true.mp h_check (k % 84) h_in
  have h_cond : (k % 84 % 2 == 1 || k % 84 == 22) = false := by
    have h_mod_2 : k % 84 % 2 = 0 := by
      have h_div : k = 84 * (k / 84) + k % 84 := (Nat.div_add_mod k 84).symm
      have hk2_even : k % 2 = 0 := h_even
      omega
    have h_neq : (k % 84 == 22) = false := by
      exact beq_false_of_ne hk2
    have h_mod_2_b : (k % 84 % 2 == 1) = false := by
      rw [h_mod_2]
      rfl
    rw [h_neq, h_mod_2_b]
    rfl
  rw [h_cond] at h_eval
  simp at h_eval
  rw [h_eval] at h_bad
  exact Bool.noConfusion h_bad

def pow_mod_loop (base exp m acc : ℕ) : ℕ :=
  match exp with
  | 0 => acc % m
  | e + 1 => pow_mod_loop base e m ((acc * base) % m)

def pow_mod_rec (base exp m : ℕ) : ℕ :=
  pow_mod_loop base exp m 1

lemma pow_mod_loop_eq (base e m acc : ℕ) : pow_mod_loop base e m acc = (acc * base ^ e) % m := by
  induction e generalizing acc with
  | zero =>
    unfold pow_mod_loop
    rw [pow_zero, mul_one]
  | succ e ih =>
    unfold pow_mod_loop
    rw [ih]
    have h1 : ((acc * base) % m * base ^ e) % m = (acc * base * base ^ e) % m := by
      exact Nat.ModEq.mul_right (base ^ e) (Nat.mod_modEq (acc * base) m)
    rw [h1]
    have h2 : acc * base * base ^ e = acc * (base ^ e * base) := by ring
    have h3 : base ^ e * base = base ^ (e + 1) := rfl
    rw [h2, h3]

lemma pow_mod_rec_eq (base e m : ℕ) : pow_mod_rec base e m = (base ^ e) % m := by
  unfold pow_mod_rec
  rw [pow_mod_loop_eq]
  rw [one_mul]

def next_y (p y : ℕ) : ℕ :=
  let y2 := (y * y) % p
  (y2 * y2) % p

lemma next_y_eq (p y : ℕ) : next_y p y = (y ^ 4) % p := by
  unfold next_y
  have hm1 : (y * y) % p ≡ (y * y) [MOD p] := Nat.mod_modEq _ _
  have hm2 : (y * y) % p * ((y * y) % p) ≡ (y * y) * (y * y) [MOD p] := Nat.ModEq.mul hm1 hm1
  have h_eq : (y * y) % p * ((y * y) % p) % p = ((y * y) * (y * y)) % p := hm2
  rw [h_eq]
  have h2 : (y * y) * (y * y) = y ^ 4 := by ring
  rw [h2]

def sq_mod_iter (p y : ℕ) : ℕ → ℕ
| 0 => y
| i + 1 => sq_mod_iter p (next_y p y) i

def check_p_fast_loop (p y fuel : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | f + 1 =>
    if (4 * y + 3) % p == 0 then false
    else check_p_fast_loop p (next_y p y) f

lemma check_p_fast_loop_sound (p y fuel i : ℕ) :
  check_p_fast_loop p y fuel = true → i < fuel → (4 * sq_mod_iter p y i + 3) % p ≠ 0 := by
  induction fuel generalizing y i with
  | zero =>
    intro _ h
    omega
  | succ f ih =>
    intro h_true h_lt
    unfold check_p_fast_loop at h_true
    revert h_true
    split
    · intro _
      contradiction
    · intro h_true
      rename_i h_cond
      have h_cond_false : (4 * y + 3) % p ≠ 0 := by
        intro hc
        have h_eq : ((4 * y + 3) % p == 0) = true := beq_iff_eq.mpr hc
        rw [h_eq] at h_cond
        contradiction
      cases i with
      | zero =>
        unfold sq_mod_iter
        exact h_cond_false
      | succ i' =>
        have h_lt' : i' < f := by omega
        have ih_res := ih (next_y p y) i' h_true h_lt'
        have h_eq : sq_mod_iter p y (i' + 1) = sq_mod_iter p (next_y p y) i' := rfl
        rw [h_eq]
        exact ih_res

lemma sq_mod_iter_eq (p y i : ℕ) :
  sq_mod_iter p (y % p) i % p = (y ^ (2 ^ (2 * i))) % p := by
  induction i generalizing y with
  | zero =>
    unfold sq_mod_iter
    have h1 : 2 * 0 = 0 := rfl
    rw [h1]
    have h2 : 2 ^ 0 = 1 := rfl
    rw [h2, pow_one]
    exact Nat.mod_mod _ _
  | succ i ih =>
    unfold sq_mod_iter
    have h_step : next_y p (y % p) = (y ^ 4) % p := by
      have h := next_y_eq p (y % p)
      have hm : (y % p) ^ 4 ≡ y ^ 4 [MOD p] := Nat.ModEq.pow 4 (Nat.mod_modEq y p)
      have h_eq : ((y % p) ^ 4) % p = (y ^ 4) % p := hm
      rw [h_eq] at h
      exact h
    rw [h_step]
    have h_ih := ih (y ^ 4)
    rw [h_ih]
    have h_pow : (y ^ 4) ^ 2 ^ (2 * i) = y ^ (2 ^ (2 * (i + 1))) := by
      rw [← pow_mul]
      have h_exp : 4 * 2 ^ (2 * i) = 2 ^ (2 * (i + 1)) := by
        have h4 : 4 = 2 ^ 2 := rfl
        rw [h4, ← pow_add]
        congr 1
        omega
      rw [h_exp]
    rw [h_pow]

lemma sq_mod_iter_eval (p x K i : ℕ) :
  sq_mod_iter p (sq_mod p x K) i % p = sq_mod p x (K + 2 * i) := by
  rw [sq_mod_eq, sq_mod_eq]
  have h := sq_mod_iter_eq p (x ^ (2 ^ K)) i
  rw [h]
  rw [← pow_mul]
  have h_exp : 2 ^ K * 2 ^ (2 * i) = 2 ^ (K + 2 * i) := by
    rw [← pow_add]
  rw [h_exp]

lemma bad_for_k_from_loop (p K fuel i : ℕ) (h_true : check_p_fast_loop p (sq_mod p 2 K) fuel = true) (h_i : i < fuel) :
  bad_for_k p (K + 2 * i) = false := by
  unfold bad_for_k
  have h_sound := check_p_fast_loop_sound p (sq_mod p 2 K) fuel i h_true h_i
  have h_eq : (sq_mod p 2 (K + 2 * i) * 4 + 3) % p = (sq_mod_iter p (sq_mod p 2 K) i % p * 4 + 3) % p := by
    rw [sq_mod_iter_eval]
  have h_eq2 : (sq_mod_iter p (sq_mod p 2 K) i % p * 4 + 3) % p = (sq_mod_iter p (sq_mod p 2 K) i * 4 + 3) % p := by
    have h_mod1 : sq_mod_iter p (sq_mod p 2 K) i % p * 4 ≡ sq_mod_iter p (sq_mod p 2 K) i * 4 [MOD p] :=
      Nat.ModEq.mul_right 4 (Nat.mod_modEq _ _)
    have h_mod2 : sq_mod_iter p (sq_mod p 2 K) i % p * 4 + 3 ≡ sq_mod_iter p (sq_mod p 2 K) i * 4 + 3 [MOD p] :=
      Nat.ModEq.add_right 3 h_mod1
    exact h_mod2
  rw [h_eq, h_eq2]
  have h_neq : (sq_mod_iter p (sq_mod p 2 K) i * 4 + 3) % p ≠ 0 := by
    have h1 : (sq_mod_iter p (sq_mod p 2 K) i * 4 + 3) % p = (4 * sq_mod_iter p (sq_mod p 2 K) i + 3) % p := by
      rw [mul_comm]
    rw [h1]
    exact h_sound
  exact beq_false_of_ne h_neq

def check_p_fast_with_P (p P : ℕ) : Bool :=
  if P == 0 then false
  else
    if P % 2 == 0 && pow_mod_rec 2 (26 + P) (p - 1) == pow_mod_rec 2 26 (p - 1) then
      check_p_fast_loop p (sq_mod p 2 26) (P / 2)
    else false

def get_period_loop (mod target fuel r curr : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | f + 1 =>
    let next_curr := (curr * 4) % mod
    if next_curr == target then r + 2
    else get_period_loop mod target f (r + 2) next_curr

def get_period (p : ℕ) : ℕ :=
  let mod := p - 1
  let target := pow_mod_rec 2 26 mod
  get_period_loop mod target 1000 0 target

def is_prime_loop (p i fuel : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | f + 1 =>
    if i * i > p then true
    else if p % i == 0 then false
    else is_prime_loop p (i + 1) f

def is_prime_fast (p : ℕ) : Bool :=
  if p < 2 then false
  else is_prime_loop p 2 p

def check_p_fast (p : ℕ) : Bool :=
  if p == 0 || p == 1 then true
  else if is_prime_fast p && p != 67 && p != 271 && p != 523 then
    check_p_fast_with_P p (get_period p)
  else true

def check_chunk (a b : ℕ) : Bool :=
  (List.range (b - a)).all (fun i => check_p_fast (a + i))

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
lemma chunk1 : check_chunk 0 200 = true := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
lemma chunk2 : check_chunk 200 400 = true := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
lemma chunk3 : check_chunk 400 600 = true := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
lemma chunk4 : check_chunk 600 800 = true := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
lemma chunk5 : check_chunk 800 1000 = true := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
lemma chunk6 : check_chunk 1000 1200 = true := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
lemma chunk7 : check_chunk 1200 1399 = true := by decide

lemma test_chunk : check_chunk 0 10 = true := by decide

lemma check_chunk_all (p : ℕ) (hp : p < 1399) : check_p_fast p = true := by
  have h1 : p < 200 ∨ (200 ≤ p ∧ p < 400) ∨ (400 ≤ p ∧ p < 600) ∨ (600 ≤ p ∧ p < 800) ∨ (800 ≤ p ∧ p < 1000) ∨ (1000 ≤ p ∧ p < 1200) ∨ (1200 ≤ p ∧ p < 1399) := by omega
  rcases h1 with h | h | h | h | h | h | h
  · have hc := chunk1
    unfold check_chunk at hc
    have h_eval := List.all_eq_true.mp hc p (List.mem_range.mpr h)
    have heq : 0 + p = p := by omega
    exact heq ▸ h_eval
  · have hc := chunk2
    unfold check_chunk at hc
    have h_eval := List.all_eq_true.mp hc (p - 200) (List.mem_range.mpr (by omega))
    have heq : 200 + (p - 200) = p := by omega
    exact heq ▸ h_eval
  · have hc := chunk3
    unfold check_chunk at hc
    have h_eval := List.all_eq_true.mp hc (p - 400) (List.mem_range.mpr (by omega))
    have heq : 400 + (p - 400) = p := by omega
    exact heq ▸ h_eval
  · have hc := chunk4
    unfold check_chunk at hc
    have h_eval := List.all_eq_true.mp hc (p - 600) (List.mem_range.mpr (by omega))
    have heq : 600 + (p - 600) = p := by omega
    exact heq ▸ h_eval
  · have hc := chunk5
    unfold check_chunk at hc
    have h_eval := List.all_eq_true.mp hc (p - 800) (List.mem_range.mpr (by omega))
    have heq : 800 + (p - 800) = p := by omega
    exact heq ▸ h_eval
  · have hc := chunk6
    unfold check_chunk at hc
    have h_eval := List.all_eq_true.mp hc (p - 1000) (List.mem_range.mpr (by omega))
    have heq : 1000 + (p - 1000) = p := by omega
    exact heq ▸ h_eval
  · have hc := chunk7
    unfold check_chunk at hc
    have h_eval := List.all_eq_true.mp hc (p - 1200) (List.mem_range.mpr (by omega))
    have heq : 1200 + (p - 1200) = p := by omega
    exact heq ▸ h_eval

lemma check_p_fast_eval (p : ℕ) (hp2 : p ≥ 2) (h_prime : is_prime_fast p = true) (h67 : p ≠ 67) (h271 : p ≠ 271) (h523 : p ≠ 523) :
  check_p_fast p = check_p_fast_with_P p (get_period p) := by
  unfold check_p_fast
  have h_p : (p == 0 || p == 1) = false := by
    have h0 : p ≠ 0 := by omega
    have h1 : p ≠ 1 := by omega
    simp [h0, h1]
  have h_cond : (is_prime_fast p && p != 67 && p != 271 && p != 523) = true := by
    have h6 : (p != 67) = true := bne_iff_ne.mpr h67
    have h2 : (p != 271) = true := bne_iff_ne.mpr h271
    have h5 : (p != 523) = true := bne_iff_ne.mpr h523
    simp [h_prime, h6, h2, h5]
  simp [h_p, h_cond]

lemma p_fast_extract (p : ℕ) (hp : check_p_fast p = true) (hp2 : p ≥ 2) (h_prime : is_prime_fast p = true) (h67 : p ≠ 67) (h271 : p ≠ 271) (h523 : p ≠ 523) :
  ∃ P, P % 2 = 0 ∧ 2^(26 + P) ≡ 2^26 [MOD (p - 1)] ∧ P > 0 ∧ ∀ r < P / 2, bad_for_k p (26 + 2 * r) = false := by
  have hp_eval := check_p_fast_eval p hp2 h_prime h67 h271 h523
  rw [hp_eval] at hp
  generalize hP : get_period p = P at hp
  generalize hB : check_p_fast_with_P p P = B at hp
  have hB_true : B = true := hp
  rw [hB_true] at hB
  unfold check_p_fast_with_P at hB
  by_cases hP0 : (P == 0) = true
  · rw [hP0] at hB
    exact False.elim (Bool.noConfusion hB)
  · have hP0_false : (P == 0) = false := eq_false_of_ne_true hP0
    rw [hP0_false] at hB
    by_cases h_cond2 : (P % 2 == 0 && pow_mod_rec 2 (26 + P) (p - 1) == pow_mod_rec 2 26 (p - 1)) = true
    · rw [h_cond2] at hB
      use P
      have h1 : P % 2 = 0 := beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp h_cond2).1
      have h2_bool := (Bool.and_eq_true _ _ |>.mp h_cond2).2
      have h2 : 2^(26 + P) ≡ 2^26 [MOD (p - 1)] := by
        have ht := beq_iff_eq.mp h2_bool
        rw [pow_mod_rec_eq, pow_mod_rec_eq] at ht
        exact ht
      have h3 : P > 0 := by
        by_contra hc
        have hz : P = 0 := by omega
        have hz_b : (P == 0) = true := beq_iff_eq.mpr hz
        rw [hz_b] at hP0_false
        exact Bool.noConfusion hP0_false
      constructor
      · exact h1
      constructor
      · exact h2
      constructor
      · exact h3
      · intro r hr
        exact bad_for_k_from_loop p 26 (P / 2) r hB hr
    · have h_cond2_false : (P % 2 == 0 && pow_mod_rec 2 (26 + P) (p - 1) == pow_mod_rec 2 26 (p - 1)) = false := eq_false_of_ne_true h_cond2
      rw [h_cond2_false] at hB
      exact False.elim (Bool.noConfusion hB)

lemma generic_period (m P k0 : ℕ) (h : 2^(k0 + P) ≡ 2^k0 [MOD m]) (k : ℕ) (hk : k ≥ k0) :
  2^(k + P) ≡ 2^k [MOD m] := by
  have h_eq : k = k0 + (k - k0) := (Nat.add_sub_cancel' hk).symm
  nth_rw 1 [h_eq]
  nth_rw 2 [h_eq]
  have h1 : k0 + (k - k0) + P = (k0 + P) + (k - k0) := by omega
  rw [h1]
  have h2 : 2^((k0 + P) + (k - k0)) = 2^(k0 + P) * 2^(k - k0) := pow_add 2 (k0 + P) (k - k0)
  rw [h2]
  have h3 : 2^(k0 + (k - k0)) = 2^k0 * 2^(k - k0) := pow_add 2 k0 (k - k0)
  rw [h3]
  exact Nat.ModEq.mul_right (2^(k - k0)) h

lemma period_mod_ind_offset (m P k0 r j : ℕ) (h_per : ∀ k ≥ k0, 2^(k+P) ≡ 2^k [MOD m]) :
  2^(k0 + r + j * P) ≡ 2^(k0 + r) [MOD m] := by
  induction j with
  | zero =>
    have h1 : k0 + r + 0 * P = k0 + r := by ring
    rw [h1]
  | succ j ih =>
    have h1 : k0 + r + (j + 1) * P = k0 + r + j * P + P := by ring
    rw [h1]
    have hp : 2^(k0 + r + j * P + P) ≡ 2^(k0 + r + j * P) [MOD m] := by
      apply h_per
      omega
    exact Nat.ModEq.trans hp ih

lemma p_mod_offset (m P k0 n : ℕ) (h_per : ∀ k ≥ k0, 2^(k+P) ≡ 2^k [MOD m]) :
  2^(k0 + n) ≡ 2^(k0 + n % P) [MOD m] := by
  have h_div : n = n % P + n / P * P := by
    have ht := Nat.mod_add_div n P
    rw [mul_comm]
    exact ht.symm
  nth_rw 1 [h_div]
  have h1 : k0 + (n % P + n / P * P) = k0 + n % P + n / P * P := by omega
  rw [h1]
  exact period_mod_ind_offset m P k0 (n % P) (n / P) h_per



lemma is_prime_loop_of_prime (p i fuel : ℕ) (hp : p.Prime) (hi : i ≥ 2) (h_fuel : fuel ≥ p) : is_prime_loop p i fuel = true := by
  norm_num[is_prime_loop] at *
  push_cast[is_prime_loop,p.prime_def]at *
  delta is_prime_loop
  exact (‹ℕ›:).rec (by bound) ( fun and A B R=>ite_eq_left_iff.2 fun and=> (if_neg (by cases hp.2 B<|B.dvd_of_mod_eq_zero<| decide_eq_true_iff.1 · with nlinarith)).trans ( (A _) (by valid))) i hi

lemma is_prime_fast_of_prime (p : ℕ) (hp : p.Prime) (hp_lt : p < 1399) : is_prime_fast p = true := by
  unfold is_prime_fast
  have hp2 : p ≥ 2 := hp.two_le
  have h_not_lt : ¬ (p < 2) := by omega
  simp [h_not_lt]
  exact is_prime_loop_of_prime p 2 p hp (by omega) (by omega)

lemma p_not_div_other (p : ℕ) (hp : p.Prime) (hp1 : p < 1399) (hp67 : p ≠ 67) (hp271 : p ≠ 271) (hp523 : p ≠ 523) (k : ℕ) (hk1 : k ≥ 26) (h_even : k % 2 = 0) : ¬ p ∣ 2^(2^k+2)+3 := by
  intro h_div
  have hp_gt2 : p > 2 := by
    by_contra h_contra
    push_neg at h_contra
    have hp2_le : p ≥ 2 := hp.two_le
    have hp2_eq : p = 2 := by omega
    rw [hp2_eq] at h_div
    have h_odd : (2^(2^k+2) + 3) % 2 = 1 := by
      have h1 : 2^(2^k+2) = 2 * 2^(2^k+1) := by
        have hz : 2^k+2 = 2^k+1+1 := by omega
        rw [hz, pow_succ, mul_comm]
      rw [h1]
      omega
    have h_div2 : (2^(2^k+2) + 3) % 2 = 0 := Nat.mod_eq_zero_of_dvd h_div
    omega
  have h_bad : bad_for_k p k = true := (bad_for_k_iff p k).mpr h_div
  have h_fast : check_p_fast p = true := check_chunk_all p hp1
  have hp2 : p ≥ 2 := hp.two_le
  have h_prime_fast : is_prime_fast p = true := is_prime_fast_of_prime p hp hp1
  have h_ext := p_fast_extract p h_fast hp2 h_prime_fast hp67 hp271 hp523
  rcases h_ext with ⟨P, hP_even, h_per_base, hP_pos, h_all⟩
  have h_per_all : ∀ k' ≥ 26, 2^(k'+P) ≡ 2^k' [MOD (p - 1)] := fun k' hk' => generic_period (p - 1) P 26 h_per_base k' hk'
  have h_mod_offset := p_mod_offset (p - 1) P 26 (k - 26) h_per_all
  have h_k_eq : 26 + (k - 26) = k := by omega
  rw [h_k_eq] at h_mod_offset
  have h_per_bad : bad_for_k p k = bad_for_k p (26 + (k - 26) % P) := by
    have h_fact : Fact (Nat.Prime p) := ⟨hp⟩
    exact bad_for_k_periodic p k (26 + (k - 26) % P) hp_gt2 h_mod_offset
  rw [h_per_bad] at h_bad
  have hr_lt : (k - 26) % P < P := Nat.mod_lt (k - 26) hP_pos
  have hr_even : (k - 26) % P % 2 = 0 := by
    have h1 : k - 26 = (k - 26) / P * P + (k - 26) % P := by
      rw [mul_comm ((k - 26) / P) P]
      exact (Nat.div_add_mod (k - 26) P).symm
    have hk2 : (k - 26) % 2 = 0 := by omega
    have hp2_even : P % 2 = 0 := hP_even
    have h_mod_2 : ((k - 26) / P * P) % 2 = 0 := by
      rw [Nat.mul_mod, hp2_even]
      simp
    have h_add : (k - 26) % 2 = (((k - 26) / P * P) % 2 + ((k - 26) % P) % 2) % 2 := by
      nth_rw 1 [h1]
      exact Nat.add_mod ((k - 26) / P * P) ((k - 26) % P) 2
    rw [hk2, h_mod_2] at h_add
    simp at h_add
    exact h_add.symm
  have h_div2 : 2 ∣ (k - 26) % P := Nat.dvd_of_mod_eq_zero hr_even
  rcases h_div2 with ⟨i, hi⟩
  have hi_eq : (k - 26) % P = 2 * i := hi
  rw [hi_eq] at h_bad
  have hi_lt : i < P / 2 := by
    have h_div_exact : 2 * (P / 2) = P := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hP_even)
    omega
  have h_good := h_all i hi_lt
  rw [h_good] at h_bad
  exact Bool.noConfusion h_bad
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (n : ℕ) : (¬covered_by_C1 (58 * n + 26) ∧ ¬covered_by_C2 (58 * n + 26) ∧ ¬covered_by_C3 (58 * n + 26)) → a (58 * n + 26) = 1399 := by
  -- EVOLVE-BLOCK-START
  intro h
  let k := 58 * n + 26
  have hk_eq : 58 * n + 26 = k := rfl
  have hk_even : k % 2 = 0 := by omega
  have hk_ge : k ≥ 26 := by omega

  have h_not_c1 : ¬ covered_by_C1 k := h.1
  have h_not_c2 : ¬ covered_by_C2 k := h.2.1
  have h_not_c3 : ¬ covered_by_C3 k := h.2.2

  have h_k_not_2 : k % 10 ≠ 2 := not_C1_implies k h_not_c1
  have h_k_not_16 : k % 36 ≠ 16 := not_C1_C2_implies k h_not_c1 h_not_c2
  have h_k_not_22 : k % 84 ≠ 22 := not_C1_C3_implies k h_not_c1 h_not_c3

  have h_not_67 := p_not_div_67 k hk_ge h_k_not_2 hk_even
  have h_not_271 := p_not_div_271 k hk_ge h_k_not_16 hk_even
  have h_not_523 := p_not_div_523 k hk_ge h_k_not_22 hk_even

  have h_1399_div : 1399 ∣ 2^(2^k+2)+3 := divides_1399 n
  have h_1399_prime : Nat.Prime 1399 := by norm_num

  have h_min_fac_le : (2^(2^k+2)+3).minFac ≤ 1399 := Nat.minFac_le_of_dvd (by norm_num) h_1399_div

  have h_min_fac_ge : (2^(2^k+2)+3).minFac ≥ 1399 := by
    by_contra h_contra
    push_neg at h_contra
    have h_neq_1 : 2^(2^k+2)+3 ≠ 1 := by omega
    have hp_prime : (2^(2^k+2)+3).minFac.Prime := Nat.minFac_prime h_neq_1
    have hp_div : (2^(2^k+2)+3).minFac ∣ 2^(2^k+2)+3 := Nat.minFac_dvd _
    rcases eq_or_ne (2^(2^k+2)+3).minFac 67 with h67 | hp_neq_67
    · have h_bad : 67 ∣ 2^(2^k+2)+3 := by rwa [← h67]
      exact h_not_67 h_bad
    rcases eq_or_ne (2^(2^k+2)+3).minFac 271 with h271 | hp_neq_271
    · have h_bad : 271 ∣ 2^(2^k+2)+3 := by rwa [← h271]
      exact h_not_271 h_bad
    rcases eq_or_ne (2^(2^k+2)+3).minFac 523 with h523 | hp_neq_523
    · have h_bad : 523 ∣ 2^(2^k+2)+3 := by rwa [← h523]
      exact h_not_523 h_bad
    have h_other := p_not_div_other ((2^(2^k+2)+3).minFac) hp_prime h_contra hp_neq_67 hp_neq_271 hp_neq_523 k hk_ge hk_even
    exact h_other hp_div

  unfold a
  linarith
  -- EVOLVE-BLOCK-END
