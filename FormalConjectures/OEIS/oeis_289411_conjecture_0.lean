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

open scoped BigOperators

/--
A289411: $\mathrm{a}(n) = \sum_{k=0}^n \mathrm{sign}(\mathrm{A007953}(5k) - \mathrm{A007953}(k))$.
$\mathrm{A007953}(n)$ is the digital sum of $n$ in base 10.
The sequence is non-negative, so the sum over $\mathbb{Z}$ is converted to $\mathbb{N}$.
-/
def A289411 (n : ℕ) : ℕ :=
  let digital_sum_ten (m : ℕ) : ℕ := (Nat.digits 10 m).sum
  (Finset.range (n + 1)).sum (fun k =>
    Int.sign ((digital_sum_ten (5 * k) : ℤ) - (digital_sum_ten k : ℤ)))
  |>.toNat

open MeasureTheory

open Polynomial

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
def S (n : ℕ) : ℕ := (Nat.digits 10 n).sum

lemma S_zero : S 0 = 0 := by norm_num[ S,id]

lemma S_lt_10 (X : ℕ) (h : X < 10) : S X = X := by rw [←eq_comm, S,X.lt_succ]at *
                                                   induction @em (X=0) with ·norm_num[X.lt_succ, *]

lemma S_step (n : ℕ) (h : 0 < n) : S n = n % 10 + S (n / 10) := by delta S
                                                                   exact(10).digits_def' (by decide) h▸rfl

lemma S_comp_9 (k A B : ℕ) (h : A + B + 1 = 10^k) : S A + S B = 9 * k := by
  induction k generalizing A B with
  | zero =>
    have : A = 0 := by omega
    have : B = 0 := by simp_all
    match A with | 0 => simp_all [S] | 1 => simp_all [S] | 2 => simp_all [S] | 3 => simp_all [S] | 4 => simp_all [S] | A + 5 => bound
  | succ k ih =>
    have h1 : A % 10 + B % 10 = 9 := by omega
    have h2 : A / 10 + B / 10 + 1 = 10^k := by omega
    have hSA : S A = A % 10 + S (A / 10) := by delta S
                                               cases A.eq_zero_or_pos with norm_num[*]
    have hSB : S B = B % 10 + S (B / 10) := by delta and S
                                               refine B.casesOn (by·norm_num) (Nat.digits_def' (by decide:10 > 1) ·.succ_pos▸rfl )
    linear_combination ih _ _ h2+ h1 +hSA +hSB

lemma S_comp_49 (n X Y : ℕ) (h : X + Y + 1 = 5 * 10^n) : S X + S Y = 9 * n + 4 := by
  induction n generalizing X Y with
  | zero =>
    have h1 : X + Y = 4 := by simp_all
    have hX : X < 10 := by omega
    have hY : Y < 10 := by omega
    have hSX : S X = X := by simp_all[S]
                             cases X.eq_zero_or_pos with (norm_num[X.mod_eq_of_lt,X.div_eq_of_lt, *])
    have hSY : S Y = Y := by simp_all[S]
                             induction Y.eq_zero_or_pos with norm_num[*,Y.mod_eq_of_lt,Y.div_eq_of_lt]
    simp_all only
  | succ n ih =>
    have h1 : X % 10 + Y % 10 = 9 := by omega
    have h2 : X / 10 + Y / 10 + 1 = 5 * 10^n := by omega
    have hSX : S X = X % 10 + S (X / 10) := by delta S
                                               cases X.eq_zero_or_pos with norm_num[*]
    have hSY : S Y = Y % 10 + S (Y / 10) := by delta S at*
                                               induction Y.eq_zero_or_pos with·norm_num [ *]
    linear_combination ih _ _ h2+‹S X = _›+‹_ = _›+h1

lemma S_comp_5j (k j : ℕ) (hk : 0 < k) (hj : j < 10^k) :
    S (5 * j) + S (5 * (10^k - 1 - j)) = 9 * k := by
  obtain ⟨k_minus_1, hk_eq⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
  have h_sum : 5 * j + 5 * (10^k - 1 - j) + 5 = 5 * 10^k := by valid
  have h_mod : (5 * j) % 10 + (5 * (10^k - 1 - j)) % 10 = 5 := by induction@@ k with ·omega
  have h_div : (5 * j) / 10 + (5 * (10^k - 1 - j)) / 10 + 1 = 5 * 10^k_minus_1 := by cases hk_eq with omega
  have hS1 : S (5 * j) = (5 * j) % 10 + S ((5 * j) / 10) := by delta and S
                                                               cases(5)*j with·norm_num
  have hS2 : S (5 * (10^k - 1 - j)) = (5 * (10^k - 1 - j)) % 10 + S ((5 * (10^k - 1 - j)) / 10) := by delta S
                                                                                                      cases(5) * ( _) with ·norm_num
  have h_IH := S_comp_49 k_minus_1 ((5 * j) / 10) ((5 * (10^k - 1 - j)) / 10) h_div
  linear_combination hS2 +h_mod +h_IH-9*hk_eq+hS1

def f (j : ℕ) : ℤ := (S (5 * j) : ℤ) - (S j : ℤ)

lemma f_symm (k j : ℕ) (hk : 0 < k) (hj : j < 10^k) :
    f j + f (10^k - 1 - j) = 0 := by
  have h1 : S (5 * j) + S (5 * (10^k - 1 - j)) = 9 * k := by
    apply S_comp_5j k j hk hj
  have h2 : S j + S (10^k - 1 - j) = 9 * k := by
    have h : j + (10^k - 1 - j) + 1 = 10^k := by rwa[j.add_sub_of_le ∘j.le_sub_one_of_lt,Nat.sub_add_cancel hj.pos]
    exact S_comp_9 k j (10^k - 1 - j) h
  delta S f at *
  omega

def sign_f (j : ℕ) : ℤ := Int.sign (f j)

lemma sign_f_symm (k j : ℕ) (hk : 0 < k) (hj : j < 10^k) :
    sign_f j + sign_f (10^k - 1 - j) = 0 := by
  have h : f (10^k - 1 - j) = - f j := by
    have := f_symm k j hk hj
    exact (eq_neg_of_add_eq_zero_right this)
  simp_all [sign_f,←geom_sum_mul_of_one_le]

lemma sum_symm_zero (H k : ℕ) (hk : 0 < k) (hH : H = 10^k / 2) (i : ℕ) (hi : i ≤ H) :
    ∑ j ∈ Finset.Ico (H - i) (H + i), sign_f j = 0 := by
  induction i with
  | zero =>
    norm_num
  | succ i ih =>
    have hi_le : i ≤ H := by refine le_of_lt hi
    have h_sum1 : ∑ j ∈ Finset.Ico (H - i - 1) (H + i), sign_f j =
        sign_f (H - i - 1) + ∑ j ∈ Finset.Ico (H - i) (H + i), sign_f j := by
      exact ( Finset.sum_eq_sum_Ico_succ_bot (by omega) _).trans (Nat.sub_add_cancel (i.sub_pos_of_lt hi)▸rfl)
    have h_sum2 : ∑ j ∈ Finset.Ico (H - i - 1) (H + i + 1), sign_f j =
        (∑ j ∈ Finset.Ico (H - i - 1) (H + i), sign_f j) + sign_f (H + i) := by
      apply Finset.sum_Ico_succ_top (by. (omega ) )
    have hj : H + i < 10^k := by omega
    have h_symm : sign_f (H - i - 1) + sign_f (H + i) = 0 := by
      have h_eq : 10^k - 1 - (H + i) = H - i - 1 := by cases k with omega
      have := sign_f_symm k (H + i) hk hj
      rwa[add_comm,<-h_eq]
    exact h_sum2.trans (by rw [h_sum1, ih hi_le, add_zero, h_symm])
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (k : ℕ) (hk : 0 < k) :
    let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → A289411 (m_k - i) = A289411 (m_k + i) := by
  -- EVOLVE-BLOCK-START
  intro m_k i hi
  have hH : m_k + 1 = 10^k / 2 := by exact (Nat.sub_add_cancel ((2).div_pos (.trans (by decide) (pow_right_monotone (by decide) (hk))) (by decide)))
  have h_sum : ∑ j ∈ Finset.Ico (m_k + 1 - i) (m_k + 1 + i), sign_f j = 0 := by
    apply sum_symm_zero (m_k + 1) k hk hH i
    refine le_add_right hi
  have h_A1 : A289411 (m_k + i) = (∑ j ∈ Finset.range (m_k + i + 1), sign_f j).toNat := by delta sign_f A289411
                                                                                           zify [ f]
                                                                                           zify[S]
  have h_A2 : A289411 (m_k - i) = (∑ j ∈ Finset.range (m_k - i + 1), sign_f j).toNat := by delta sign_f A289411 at*
                                                                                           rfl
  have h_range_split : ∑ j ∈ Finset.range (m_k + i + 1), sign_f j =
      (∑ j ∈ Finset.range (m_k - i + 1), sign_f j) + ∑ j ∈ Finset.Ico (m_k - i + 1) (m_k + i + 1), sign_f j := by
    exact ( Finset.sum_range_add_sum_Ico sign_f (by(omega))).symm
  have h_eq : m_k + 1 - i = m_k - i + 1 := by use m_k.succ_sub hi
  have h_eq2 : m_k + 1 + i = m_k + i + 1 := by abel
  simp_all-contextual only[add_zero]
  -- EVOLVE-BLOCK-END
