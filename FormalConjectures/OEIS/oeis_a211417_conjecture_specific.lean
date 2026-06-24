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
Integral factorial ratio sequence:
$$a(n) = \frac{(30n)! n!}{(15n)! (10n)! (6n)!}$$
-/
def a (n : ℕ) : ℕ :=
  (Nat.factorial (30 * n) * Nat.factorial n) /
  (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n))

open Nat Int Finset

def coprime_indices (r : ℕ) : Finset ℕ :=
  (Finset.range (r + 1)).filter (fun i => 1 ≤ i ∧ Nat.gcd i 30 = 1)

/--
The product term in the denominator of the general conjecture:
$$\prod_{i = 1..r, i \text{ coprime to } 30} (30n - i)$$
We define this in ℤ to handle the $n=0$ case where $30n-i$ in the product might be negative.
-/
def divisor_product (n r : ℕ) : ℤ :=
  (coprime_indices r).prod (fun i : ℕ => 30 * (n : ℤ) - (i : ℤ))

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
lemma helper_div (c n M : ℕ) : c * n / M = c * (n / M) + c * (n % M) / M := by
  exact M.eq_zero_or_pos.elim (by simp_all) (by rw [← M.mul_add_div ·,mul_left_comm,←mul_add,Nat.div_add_mod])

lemma div_half (s y : ℕ) : (15 * s) / y = ((30 * s) / y) / 2 := by
  exact (2).mul_div_mul_right _ _ (by decide)▸Nat.mul_right_comm _ _ _▸(Nat.div_div_eq_div_mul _ _ _).symm

lemma div_third (s y : ℕ) : (10 * s) / y = ((30 * s) / y) / 3 := by
  exact (3).mul_div_mul_right _ _ (by decide)▸Nat.mul_right_comm _ _ _▸ ((Nat.div_div_eq_div_mul _ _ _).symm)

lemma div_fifth (s y : ℕ) : (6 * s) / y = ((30 * s) / y) / 5 := by
  rw [Nat.div_div_eq_div_mul, ←Nat.mul_div_mul_right _ _ (by decide:0<5),Nat.mul_right_comm]

lemma k_ineq (k : ℕ) (hk : k ≤ 29) : k / 2 + k / 3 + k / 5 ≤ k := by
  classical decide +revert

lemma c_eq (q r : ℕ) (hr : r = 1 ∨ r = 7 ∨ r = 11 ∨ r = 13 ∨ r = 17 ∨ r = 19 ∨ r = 23 ∨ r = 29) :
  (30*q + r)/2 + (30*q + r)/3 + (30*q + r)/5 + 1 = 31*q + r := by
  omega

lemma c_mod_30 (c y : ℕ) (h : (c * y) % 30 = 29) : c % 30 = 1 ∨ c % 30 = 7 ∨ c % 30 = 11 ∨ c % 30 = 13 ∨ c % 30 = 17 ∨ c % 30 = 19 ∨ c % 30 = 23 ∨ c % 30 = 29 := by
  use (by_contra fun and=>absurd (h▸(2).mod_mod_of_dvd _) fun and=>absurd (h▸(3).mod_mod_of_dvd _) fun and=>absurd (c.mul_mod y 30) ? _)
  cases eq_or_ne (c%30) 25
  · refine (by assumption▸by valid)
  cases eq_or_ne (c%30) 27
  · use‹_›▸by valid
  haveI := (Classical.decEq ℝ)
  obtain ⟨a, _⟩| ⟨a, _⟩:=(c%30).even_or_odd
  · use‹_›▸a.add_mul _ _▸by valid
  · use‹_›▸by match a with|0|1|2|3|4|5|6|7|8|9|10|11 | S+12=>omega

lemma n_div_y (n c y q r : ℕ) (hy : y ≥ 2) (hc1 : 30 * n = c * y + 1) (hc2 : c = 30 * q + r) (hr : r ≤ 29) : n / y = q := by
  exact (q.div_eq_of_lt_le (by match hc2▸add_mul _ _ y,mul_assoc 30 q y with|A, B=>omega) (by linarith only[hc2▸hc1,hy, mul_le_mul_left' hr y]))

lemma h8_lemma (n y : ℕ) (hy : y > 0) : 30 * (n % y) / y ≤ 29 := by
  exact (Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by push_cast[Nat.mul_lt_mul_left _,mul_comm y,n.mod_lt hy])))

lemma f_ge_zero (n y : ℕ) (hy : y > 0) : (15*n)/y + (10*n)/y + (6*n)/y ≤ (30*n)/y + n/y := by
  have h1 : 15 * n / y = 15 * (n / y) + 15 * (n % y) / y := helper_div 15 n y
  have h2 : 10 * n / y = 10 * (n / y) + 10 * (n % y) / y := helper_div 10 n y
  have h3 : 6 * n / y = 6 * (n / y) + 6 * (n % y) / y := helper_div 6 n y
  have h4 : 30 * n / y = 30 * (n / y) + 30 * (n % y) / y := helper_div 30 n y
  have h5 : 15 * (n % y) / y = (30 * (n % y) / y) / 2 := div_half (n % y) y
  have h6 : 10 * (n % y) / y = (30 * (n % y) / y) / 3 := div_third (n % y) y
  have h7 : 6 * (n % y) / y = (30 * (n % y) / y) / 5 := div_fifth (n % y) y
  have h8 : 30 * (n % y) / y ≤ 29 := h8_lemma n y hy
  have h9 : (30 * (n % y) / y) / 2 + (30 * (n % y) / y) / 3 + (30 * (n % y) / y) / 5 ≤ 30 * (n % y) / y := k_ineq (30 * (n % y) / y) h8
  omega

lemma f_nat_eq_one_helper (n y c q r : ℕ) (hy : y ≥ 2) (hc1 : 30 * n = c * y + 1) (hc2 : c = 30 * q + r) (hr : r ≤ 29) (hr2 : r = 1 ∨ r = 7 ∨ r = 11 ∨ r = 13 ∨ r = 17 ∨ r = 19 ∨ r = 23 ∨ r = 29) :
  (30*n)/y + n/y = (15*n)/y + (10*n)/y + (6*n)/y + 1 := by
  have h1 : 30 * n / y = c := by norm_num[hc1,y.mul_add_div ∘hy.trans',Nat.div_eq_of_lt hy,c.mul_comm]
  have h2 : n / y = q := n_div_y n c y q r hy hc1 hc2 hr
  have h3 : (15*n)/y = c/2 := by
    rw [div_half n y, h1]
  have h4 : (10*n)/y = c/3 := by
    rw [div_third n y, h1]
  have h5 : (6*n)/y = c/5 := by
    rw [div_fifth n y, h1]
  rw [h1, h2, h3, h4, h5, hc2]
  have h6 := c_eq q r hr2
  omega

lemma padic_fac_test (p n : ℕ) [Fact p.Prime] : padicValNat p (Nat.factorial n) = ∑ i ∈ Finset.Ico 1 (n + 1), n / p^i := by
  apply(padicValNat_factorial (Nat.succ_le_succ (p.log_le_self n)))

def f_nat (x d : ℕ) : ℤ :=
  ((30 * x) / d : ℤ) + (x / d : ℤ) - ((15 * x) / d : ℤ) - ((10 * x) / d : ℤ) - ((6 * x) / d : ℤ)

lemma f_nat_nonneg (x d : ℕ) : f_nat x d ≥ 0 := by
  by_cases hd : d = 0
  · subst hd
    unfold f_nat
    simp
  · have hd_pos : d > 0 := Nat.pos_of_ne_zero hd
    have h := f_ge_zero x d hd_pos
    unfold f_nat
    zify at *
    omega

lemma f_nat_eq_one (n p k : ℕ) (hp : p.Prime) (hk : k ≥ 1) (h_mod : (30 * n) % (p ^ k) = 1) :
  f_nat n (p ^ k) = 1 := by
  have hy : p ^ k ≥ 2 := by apply (p.pow_lt_pow_right) hp.one_lt hk
  have hy_pos : p ^ k > 0 := by omega
  have hc1 : 30 * n = (30 * n / (p ^ k)) * (p ^ k) + 1 := by rw [← h_mod,Nat.div_add_mod']
  have hy_mod : ((30 * n / (p ^ k)) * (p ^ k)) % 30 = 29 := by try omega
  have hr2 : (30 * n / (p ^ k)) % 30 = 1 ∨ (30 * n / (p ^ k)) % 30 = 7 ∨ (30 * n / (p ^ k)) % 30 = 11 ∨ (30 * n / (p ^ k)) % 30 = 13 ∨ (30 * n / (p ^ k)) % 30 = 17 ∨ (30 * n / (p ^ k)) % 30 = 19 ∨ (30 * n / (p ^ k)) % 30 = 23 ∨ (30 * n / (p ^ k)) % 30 = 29 := c_mod_30 (30 * n / (p ^ k)) (p ^ k) hy_mod
  have hr : (30 * n / (p ^ k)) % 30 ≤ 29 := by omega
  have hc2 : 30 * n / (p ^ k) = 30 * ((30 * n / (p ^ k)) / 30) + (30 * n / (p ^ k)) % 30 := by rw [Nat.div_add_mod]
  have h_eq := f_nat_eq_one_helper n (p ^ k) (30 * n / (p ^ k)) ((30 * n / (p ^ k)) / 30) ((30 * n / (p ^ k)) % 30) hy hc1 hc2 hr hr2
  have h_ge : (15 * n) / p ^ k + (10 * n) / p ^ k + (6 * n) / p ^ k ≤ (30 * n) / p ^ k + n / p ^ k := f_ge_zero n (p^k) hy_pos
  unfold f_nat
  zify at *
  omega

lemma val_L_minus_val_A (n p : ℕ) (hp : p.Prime) :
  (padicValNat p (30 * n).factorial : ℤ) + (padicValNat p n.factorial : ℤ) -
  ((padicValNat p (15 * n).factorial : ℤ) + (padicValNat p (10 * n).factorial : ℤ) + (padicValNat p (6 * n).factorial : ℤ)) =
  ∑ k ∈ Finset.Ico 1 (30 * n + 1), f_nat n (p ^ k) := by
  delta f_nat decide
  push_cast[Fact.mk hp, sub_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  repeat rw_mod_cast[match Fact.mk hp with|k=>padicValNat_factorial (Nat.succ_le_succ ((p.log_le_self _).trans ( (by valid:_≤30*n))))]

lemma padicVal_of_30n_minus_1 (n p : ℕ) (hp : p.Prime) (hn : n > 0) :
  (padicValNat p (30 * n - 1) : ℤ) = ∑ k ∈ Finset.Ico 1 (30 * n + 1), if (p ^ k) ∣ (30 * n - 1) then (1 : ℤ) else (0 : ℤ) := by
  norm_num[padicValNat_dvd_iff_le (by omega:30*n-1≠0),Fact.mk hp,←Nat.factorization_def _,← Finset.mem_Icc,hp.pow_dvd_iff_le_factorization (by omega:30*n-1≠0),hn]
  exact(((congr_arg _) (Finset.ext (by simp_all[·.lt_succ,((30*n-1).factorization_def hp▸Nat.factorization_lt p (by cases hn with cases.)).le.trans (Nat.sub_le _ _)|>.trans']))).trans ((1).card_Icc (padicValNat _ _))).symm

lemma f_nat_ge_indicator (n p k : ℕ) (hp : p.Prime) (hk : k ≥ 1) (hn : n > 0) :
  (if (p ^ k) ∣ (30 * n - 1) then (1 : ℤ) else (0 : ℤ)) ≤ f_nat n (p ^ k) := by
  by_cases h : (p ^ k) ∣ (30 * n - 1)
  · have h1 : (30 * n) % (p ^ k) = 1 := by induction ↑hn with apply(h).modEq_zero_nat.add_right (1)▸Nat.mod_eq_of_lt (p.pow_lt_pow_right hp.one_lt (↑hk ) )
    have h2 : f_nat n (p ^ k) = 1 := f_nat_eq_one n p k hp hk h1
    rw [if_pos h]
    omega
  · have h1 : f_nat n (p ^ k) ≥ 0 := f_nat_nonneg n (p ^ k)
    rw [if_neg h]
    omega

lemma padic_val_div (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (h : ∀ p : ℕ, p.Prime → padicValNat p a ≤ padicValNat p b) : a ∣ b := by
  exact (a.factorization_le_iff_dvd ha hb).mp (by cases@em ·.Prime with norm_num [Nat.factorization_def _, *])

def R_def (n : ℕ) : ℕ := (30 * n - 1) * ((15 * n).factorial * (10 * n).factorial * (6 * n).factorial)
def L_def (n : ℕ) : ℕ := (30 * n).factorial * n.factorial

lemma L_def_ne_zero (n : ℕ) : L_def n ≠ 0 := by rw [←ne_comm, Ne, L_def]
                                                positivity

lemma R_def_val (n p : ℕ) (hn : n > 0) (hp : p.Prime) : (padicValNat p (R_def n) : ℤ) = (padicValNat p (30 * n - 1) : ℤ) + (padicValNat p ((15 * n).factorial * (10 * n).factorial * (6 * n).factorial) : ℤ) := by simp_all[padicValNat.mul (by cases (n : ℕ) with tauto: (30) *(n)-1≠0),Fact.mk, R_def, false,Nat.factorial_ne_zero]

lemma L_def_val (n p : ℕ) (hn : n > 0) (hp : p.Prime) : (padicValNat p (L_def n) : ℤ) = (padicValNat p (30 * n).factorial : ℤ) + (padicValNat p n.factorial : ℤ) := by exact (congr_arg _) (by match Fact.mk hp with | S =>exact (padicValNat.mul (by·positivity ) ) (n : ℕ).factorial_ne_zero)

lemma A_val (n p : ℕ) (hn : n > 0) (hp : p.Prime) : (padicValNat p ((15 * n).factorial * (10 * n).factorial * (6 * n).factorial) : ℤ) =
      (padicValNat p (15 * n).factorial : ℤ) + (padicValNat p (10 * n).factorial : ℤ) + (padicValNat p (6 * n).factorial : ℤ) := by simp_all[padicValNat.mul,Fact.mk _,Nat.factorial_ne_zero]

lemma L_div (n : ℕ) (hn : n > 0) : R_def n ∣ L_def n := by
  have hR : R_def n ≠ 0 := by
    have h1 : 30 * n - 1 > 0 := by omega
    have h2 : ((15 * n).factorial * (10 * n).factorial * (6 * n).factorial) > 0 := by positivity
    exact Nat.ne_of_gt (Nat.mul_pos h1 h2)
  have hL : L_def n ≠ 0 := L_def_ne_zero n
  have H_padic : ∀ p : ℕ, p.Prime → padicValNat p (R_def n) ≤ padicValNat p (L_def n) := by
    intro p hp
    have h1 := R_def_val n p hn hp
    have h2 := L_def_val n p hn hp
    have h3 := A_val n p hn hp
    have h4 : (padicValNat p (L_def n) : ℤ) - (padicValNat p ((15 * n).factorial * (10 * n).factorial * (6 * n).factorial) : ℤ) =
      ∑ k ∈ Finset.Ico 1 (30 * n + 1), f_nat n (p ^ k) := by
      rw [h2, h3]
      exact val_L_minus_val_A n p hp
    have h5 : (padicValNat p (30 * n - 1) : ℤ) =
      ∑ k ∈ Finset.Ico 1 (30 * n + 1), if (p ^ k) ∣ (30 * n - 1) then (1 : ℤ) else (0 : ℤ) := padicVal_of_30n_minus_1 n p hp hn
    have h6 : (padicValNat p (30 * n - 1) : ℤ) ≤ (padicValNat p (L_def n) : ℤ) - (padicValNat p ((15 * n).factorial * (10 * n).factorial * (6 * n).factorial) : ℤ) := by
      rw [h4, h5]
      apply Finset.sum_le_sum
      intro k hk
      have hk1 : k ≥ 1 := by exact (Finset.mem_Ico.1 hk).1
      exact f_nat_ge_indicator n p k hp hk1 hn
    omega
  have h_div := padic_val_div (R_def n) (L_def n) hR hL H_padic
  exact h_div

lemma target_nat (n : ℕ) (hn : n > 0) : (30 * n - 1) ∣ a n := by
  have H : R_def n ∣ L_def n := L_div n hn
  delta a and R_def and L_def at *
  exact (Nat.dvd_div_of_mul_dvd (by rwa [mul_comm]))
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (n : ℕ) : (30 * (n : ℤ) - 1) ∣ (a n : ℤ) := by
  -- EVOLVE-BLOCK-START
  cases n with
  | zero =>
    -- n = 0 case: 30*0 - 1 = -1, a 0 = 1, so -1 | 1
    decide
  | succ n' =>
    -- n > 0 case
    have hn : n' + 1 > 0 := by exact Nat.succ_pos n'
    have h_nat := target_nat (n' + 1) hn
    simp_all only [push_cast, mul_pos, (by decide :30>0), ←Int.ofNat_dvd]
  -- EVOLVE-BLOCK-END
