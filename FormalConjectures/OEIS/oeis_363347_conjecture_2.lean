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




open Rat Nat

/--
Helper function for A363347, which computes the denominator $R_k(n)$ of the continued fraction expression.
For $2 \le k \le n-1$, $R_k(n)$ is defined recursively:
$$R_k(n) = k - \frac{k+1}{R_{k+1}(n)}$$
The base case is $R_{n-1}(n) = (n-1) - \frac{n}{-4}$.
-/
def continued_fraction_denominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else
    -- The recursive descent involves terms from $k=n-1$ down to $k=2$.
    if 2 ≤ k ∧ k ≤ n - 1 then
      -- Base Case: k = n - 1.
      if k = n - 1 then
        -- R_{n-1} = (n-1) + n/4
        (k : ℚ) + (n : ℚ) / 4
      -- Recursive Step: 2 <= k < n - 1.
      else
        let R_next := continued_fraction_denominator n (k + 1)
        -- R_k = k - (k+1) / R_{k+1}
        (k : ℚ) - (k + 1 : ℚ) / R_next
    else 0
termination_by n - k

/--
A363347: Denominator of the continued fraction
$$\frac{1}{2 - \frac{3}{3 - \frac{4}{4 - \frac{5}{\dots - \frac{n-1}{(n-1) - \frac{n}{-4}}}}}} $$
The value of the continued fraction is $C_n = 1/R_2(n)$. If $R_2(n) = N/D$ in reduced form, $C_n = D/N$.
The sequence $a(n)$ is the denominator of the final fraction, which is $\vert N \vert$.
-/
noncomputable def A363347 (n : ℕ) : ℕ :=
  if n ≤ 2 then 0 -- The sequence is indexed starting from $n=3$.
  else
    let R2 := continued_fraction_denominator n 2
    R2.num.natAbs

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
def Z_seq : ℕ → ℤ
| 0 => 0
| 1 => 0
| 2 => 0 -- not used
| 3 => 0
| 4 => 1
| k + 5 => (k + 3) * (Z_seq (k + 4) - Z_seq (k + 3))

def U_val (k : ℕ) : ℚ :=
  if k < 2 then 0 else 2 * (k - 2 : ℚ) / (Nat.factorial (k - 1) : ℚ)

lemma U_val_rec (k : ℕ) (hk : k ≥ 2) :
  U_val k = (k : ℚ) * U_val (k + 1) - (k + 1 : ℚ) * U_val (k + 2) := by
  delta U_val
  norm_num[mul_comm (2 :ℚ),hk.trans',add_sub_right_comm, mul_add, mul_div, mul_div_mul_left _,mt hk.trans_eq, if_neg,k.cast_add_one_ne_zero,k.sub_add_cancel (le_of_lt hk)▸Nat.factorial_succ _,.!]
  use (if_neg (by valid : ¬ (k + 1)<2))▸by ring

def A_seq (n k : ℕ) : ℚ :=
  if k ≥ n then 4
  else if k = n - 1 then 5 * (n : ℚ) - 4
  else (k : ℚ) * A_seq n (k + 1) - (k + 1 : ℚ) * A_seq n (k + 2)
termination_by n - k

lemma A_seq_rec (n k : ℕ) (hk : k + 2 ≤ n) :
  A_seq n k = (k : ℚ) * A_seq n (k + 1) - (k + 1 : ℚ) * A_seq n (k + 2) := by
  rewrite[ A_seq, sub_eq_add_neg]
  repeat rw[if_neg (by valid)]

lemma Z_seq_rec (k : ℕ) (hk : k ≥ 3) :
  Z_seq (k + 2) = (k : ℤ) * (Z_seq (k + 1) - Z_seq k) := by
  rw [← (k : ℕ).sub_add_cancel hk, Z_seq]
  rfl

lemma W_rec (n k : ℕ) (hk : 2 ≤ k) (hkn : k + 2 ≤ n) :
  A_seq n k * U_val (k + 1) - U_val k * A_seq n (k + 1) =
  (k + 1 : ℚ) * (A_seq n (k + 1) * U_val (k + 2) - U_val (k + 1) * A_seq n (k + 2)) := by
  delta Nat.cast U_val A_seq
  use WellFounded.Nat.fix_eq _ _ _▸if_neg (by valid : ¬ (k + 1)<2)▸if_neg hk.not_gt▸match k with | S+1=>(@Nat.cast_mul Rat _ _ _).symm▸(@Nat.cast_mul Rat _ _ _).symm▸(@Nat.cast_succ Rat _ _).symm▸symm ?_
  push_cast[.!, not_lt.2, (by valid: S+1≤n∧S+1≠n-1)]
  exact (mul_div_mul_left _) (S ! :ℚ) S.cast_add_one_ne_zero▸dif_neg (by valid : ¬ n≤S+1)▸.trans (by rw [mul_sub, mul_left_comm, mul_div, mul_div_mul_left _ _ (by((((norm_cast)))))]) (by·ring1)

lemma W_val (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n - 1) :
  (Nat.factorial k : ℚ) / 2 * (A_seq n k * U_val (k + 1) - U_val k * A_seq n (k + 1)) =
  (Nat.factorial (n - 1) : ℚ) / 2 * (A_seq n (n - 1) * U_val n - U_val (n - 1) * A_seq n n) := by
  obtain ⟨s, rfl⟩:=n.exists_eq_succ_of_ne_zero (by cases ·▸hk.trans hkn)
  field_simp [hkn]
  simp_all![U_val]
  norm_num[*, mul_sub,hk.trans',hkn.trans',add_sub_assoc,mul_left_comm (( _)!:ℚ),←mul_assoc, mul_div_cancel₀, if_neg,←Nat.factorial_mul_descFactorial<|le_of_lt hk,Nat.factorial_ne_zero]
  field_simp [hkn.trans',mul_assoc, if_neg]
  have : ∀ a ∈ Finset.Icc k s,A_seq (s+1) k*2*(k+-1)-k*(k*2-4)* A_seq (s+1) (k + 1)=2* A_seq (s+1) a*(a+-1) - (2 *a-4)* a* A_seq (s+1) (a+1)
  · use fun and=>And.elim ↑(k.le_induction (by bound) (fun R M K V=>symm (K (by valid)▸.trans (by rw [ R.cast_succ]) ?_)) _) ∘ Finset.mem_Icc.1
    delta A_seq
    obtain ⟨@c⟩ :=V.eq_or_lt
    · push_cast[WellFounded.Nat.fix_eq, add_assoc, R.add_sub_cancel_left, not_le.2, R.lt_succ_self,refl]
      exact (dif_neg) (Nat.lt_irrefl _)▸symm (.trans (by rw [dif_neg (by valid),dif_neg R.lt_succ_self.ne]) (by ring))
    · exact (symm (.trans (by rw [WellFounded.Nat.fix_eq, dif_neg (by valid),dif_neg (by valid)]) (by ring)))
  · exact (if_neg (by valid : ¬ (k + 1)<2))▸(this s) (by(norm_num [*]))▸if_neg (by valid : ¬s+1 <2)▸ (by cases hk.trans hkn with apply Nat.cast_mul : (s ! : Rat)=s*(s-1)!)▸by(ring!)

lemma X_rec (n k : ℕ) (hk : 3 ≤ k) (hkn : k + 2 ≤ n) :
  A_seq n (k + 2) * (Nat.factorial (k + 1) : ℚ) / 2 =
  (k : ℚ) * (A_seq n (k + 1) * (Nat.factorial k : ℚ) / 2 - A_seq n k * (Nat.factorial (k - 1) : ℚ) / 2) := by
  have hk_rec : A_seq n k = (k : ℚ) * A_seq n (k + 1) - (k + 1 : ℚ) * A_seq n (k + 2) := A_seq_rec n k hkn
  have h_factk : (Nat.factorial k : ℚ) = (k : ℚ) * (Nat.factorial (k - 1) : ℚ) := by induction hk with apply Nat.cast_mul
  have h_factk1 : (Nat.factorial (k + 1) : ℚ) = (k + 1 : ℚ) * (Nat.factorial k : ℚ) := by zify[.!]
  refine‹_›▸hk_rec▸h_factk▸by ring

def Y_val (n k : ℕ) : ℚ := A_seq n k * (Nat.factorial (k - 1) : ℚ) / 2
def R_val (n k : ℕ) : ℚ := (k - 2 : ℚ) * A_seq n 3 - (Z_seq k : ℚ) * A_seq n 2

lemma Y_rec (n k : ℕ) (hk : 3 ≤ k) (hkn : k + 2 ≤ n) :
  Y_val n (k + 2) = (k : ℚ) * (Y_val n (k + 1) - Y_val n k) := X_rec n k hk hkn

lemma R_rec (n k : ℕ) (hk : 3 ≤ k) :
  R_val n (k + 2) = (k : ℚ) * (R_val n (k + 1) - R_val n k) := by
  rw [←mul_comm, R_val, R_val, R_val]
  replace hk: Z_seq @(k+2) = (Z_seq (k + 1)-Z_seq k) * (k : ℕ)
  · delta Z_seq
    match k with | S+3=>apply mul_comm
  · exact (.trans ( by aesop) (.symm ((.trans (by rw [ k.cast_succ]) (by ·ring)))))

lemma Y_eq_R_3 (n : ℕ) : Y_val n 3 = R_val n 3 := by
  have hy3 : Y_val n 3 = A_seq n 3 * (Nat.factorial 2 : ℚ) / 2 := by simp_all![Y_val]
  have hr3 : R_val n 3 = (3 - 2 : ℚ) * A_seq n 3 - (Z_seq 3 : ℚ) * A_seq n 2 := by norm_num [R_val]
  have hz3 : Z_seq 3 = 0 := by norm_num[Z_seq]
  have hy3_eq : Y_val n 3 = A_seq n 3 := by linear_combination hy3
  have hr3_eq : R_val n 3 = A_seq n 3 := by norm_num [*]
  exact hy3_eq.trans hr3_eq.symm

lemma Y_eq_R_pair (n m : ℕ) (hkn : m + 4 ≤ n) :
  Y_val n (m + 3) = R_val n (m + 3) ∧ Y_val n (m + 4) = R_val n (m + 4) := by
  induction' m with m ih
  · have hy3 : Y_val n 3 = A_seq n 3 * (Nat.factorial 2 : ℚ) / 2 := by simp_all![Y_val]
    have hr3 : R_val n 3 = (3 - 2 : ℚ) * A_seq n 3 - (Z_seq 3 : ℚ) * A_seq n 2 := by norm_num[Z_seq,R_val]
    have hz3 : Z_seq 3 = 0 := by norm_num[Z_seq]
    have hy3_eq : Y_val n 3 = A_seq n 3 := by norm_num[ hy3]
    have hr3_eq : R_val n 3 = A_seq n 3 := by norm_num [ *]
    have heq3 : Y_val n 3 = R_val n 3 := by convert rfl
    have hk2 : 2 + 2 ≤ n := by congr
    have ha2 : A_seq n 2 = (2 : ℚ) * A_seq n (2 + 1) - (2 + 1 : ℚ) * A_seq n (2 + 2) := A_seq_rec n 2 hk2
    have hy4 : Y_val n 4 = A_seq n 4 * (Nat.factorial 3 : ℚ) / 2 := by norm_num[Y_val, true,ha2,hy3_eq, mul_div_assoc _,mul_comm]
    have hy4_eq : Y_val n 4 = 3 * A_seq n 4 := by linear_combination2 hy4
    have hr4 : R_val n 4 = (4 - 2 : ℚ) * A_seq n 3 - (Z_seq 4 : ℚ) * A_seq n 2 := by norm_num[*, R_val,Z_seq]
    have hz4 : Z_seq 4 = 1 := by norm_num [ Z_seq]
    have hr4_eq : R_val n 4 = 2 * A_seq n 3 - A_seq n 2 := by norm_num[hz4,hr4]
    have heq4 : Y_val n 4 = R_val n 4 := by norm_num [by assumption, hy4_eq, ha2]
    exact ⟨heq3, heq4⟩
  · have hkn_prev : m + 4 ≤ n := by omega
    have ih_val := ih hkn_prev
    have hk1 : 3 ≤ m + 3 := by push_cast
    have hk2 : m + 3 + 2 ≤ n := by valid
    have h_y_rec := Y_rec n (m + 3) hk1 hk2
    have h_r_rec := R_rec n (m + 3) hk1
    have heq5 : Y_val n (m + 5) = R_val n (m + 5) := by zify [*]
    exact ⟨ih_val.2, heq5⟩

lemma Y_eq_R (n m : ℕ) (hkn : m + 3 ≤ n) :
  Y_val n (m + 3) = R_val n (m + 3) := by
  cases m with
  | zero => exact Y_eq_R_3 n
  | succ m_prev =>
    have h : m_prev + 4 ≤ n := by omega
    exact (Y_eq_R_pair n m_prev h).2

lemma A_seq_Z_seq (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n) :
  A_seq n k * (Nat.factorial (k - 1) : ℚ) / 2 =
  (k - 2 : ℚ) * A_seq n 3 - (Z_seq k : ℚ) * A_seq n 2 := by
  have hm : ∃ m, k = m + 3 := by exact (Nat.exists_eq_add_of_le') hk
  rcases hm with ⟨m, rfl⟩
  have hy := Y_eq_R n m hkn
  norm_num[Y_val,R_val, A.-heq_of_eq, mul_div_assoc _,Z_seq, false,_root_.Nat.succ_sub_one _,add_sub_assoc, false,·!]at *
  omega

lemma A_seq_n (n : ℕ) (hn : 3 ≤ n) :
  A_seq n n * (Nat.factorial (n - 1) : ℚ) / 2 =
  (n - 2 : ℚ) * A_seq n 3 - (Z_seq n : ℚ) * A_seq n 2 := by
  have hk : 3 ≤ n := hn
  have hkn : n ≤ n := by rfl
  exact A_seq_Z_seq n n hk hkn

def A_int (n k : ℕ) : ℤ :=
  if k ≥ n then 4
  else if k = n - 1 then 5 * (n : ℤ) - 4
  else (k : ℤ) * A_int n (k + 1) - (k + 1 : ℤ) * A_int n (k + 2)
termination_by n - k

lemma A_int_eq_d (d : ℕ) : ∀ n k : ℕ, n - k ≤ d → A_seq n k = (A_int n k : ℚ) := by
  induction d with
  | zero =>
    intro n k hd
    have hk : k ≥ n := by omega
    unfold A_seq A_int
    split
    · rfl
    · contradiction
  | succ d ih =>
    intro n k hd
    unfold A_seq A_int
    split
    · rfl
    · split
      · push_cast; rfl
      · have h1 : n - (k + 1) ≤ d := by omega
        have h2 : n - (k + 2) ≤ d := by omega
        have eq1 := ih n (k + 1) h1
        have eq2 := ih n (k + 2) h2
        rw [eq1, eq2]
        push_cast
        rfl

lemma A_int_eq (n k : ℕ) : A_seq n k = (A_int n k : ℚ) := by
  exact A_int_eq_d (n - k) n k (by rfl)

lemma A2_eq (n : ℕ) (hn : n ≥ 3) : A_seq n 2 = (n : ℚ)^2 + 2 * (n : ℚ) - 4 := by
  have hk1 : 2 ≤ 2 := by constructor
  have hk2 : 2 ≤ n - 1 := by omega
  have hw : (Nat.factorial 2 : ℚ) / 2 * (A_seq n 2 * U_val 3 - U_val 2 * A_seq n 3) =
            (Nat.factorial (n - 1) : ℚ) / 2 * (A_seq n (n - 1) * U_val n - U_val (n - 1) * A_seq n n) := W_val n 2 hk1 hk2
  have hu2 : U_val 2 = 0 := by norm_num [U_val]
  have hu3 : U_val 3 = 1 := by norm_num[U_val]
  have han : A_seq n n = 4 := by delta A_seq U_val at *
                                 push_cast [WellFounded.Nat.fix_eq,refl]
  have han1 : A_seq n (n - 1) = 5 * (n : ℚ) - 4 := by delta A_seq
                                                      rw[WellFounded.Nat.fix_eq, dif_neg (by valid),dif_pos rfl]
  have hun : U_val n = 2 * (n - 2 : ℚ) / (Nat.factorial (n - 1) : ℚ) := by delta U_val
                                                                           refine (if_neg (by valid ) )
  have hun1 : U_val (n - 1) = 2 * (n - 3 : ℚ) / (Nat.factorial (n - 2) : ℚ) := by delta U_val at*
                                                                                  exact (.trans (by rw [Nat.cast_pred (by valid),if_neg hk2.not_gt]) (by ring!))
  have h_fact : (Nat.factorial 2 : ℚ) / 2 = 1 := by norm_num
  have h_fact2 : (Nat.factorial (n - 1) : ℚ) = (n - 1 : ℚ) * (Nat.factorial (n - 2) : ℚ) := by match(n) with | S+2 =>norm_num only[push_cast, S.add_sub_cancel _,add_sub_assoc,·!, true,Nat.succ_sub_one]
  have hw2 : A_seq n 2 = (Nat.factorial (n - 1) : ℚ) / 2 * ((5 * (n : ℚ) - 4) * (2 * (n - 2 : ℚ) / (Nat.factorial (n - 1) : ℚ)) - (2 * (n - 3 : ℚ) / (Nat.factorial (n - 2) : ℚ)) * 4) := by simp_all only[one_mul,zero_mul,mul_one, sub_zero]
  have hw3 : A_seq n 2 = (5 * (n : ℚ) - 4) * (n - 2 : ℚ) - 4 * (n - 1 : ℚ) * (n - 3 : ℚ) := by exact (hw2)▸h_fact2▸.trans (by ring) (congr_arg₂ _ ((mul_div_cancel₀ _) (@h_fact2▸Nat.cast_ne_zero.2 (by positivity))) ((mul_div_cancel₀ _) (@Nat.cast_ne_zero.2 (n-2).factorial_ne_zero)))
  linear_combination2 (hw3)

lemma A_seq_3_2_bound (n : ℕ) (hn : 3 ≤ n) :
  2 * (Nat.factorial (n - 1) : ℚ) = (n - 2 : ℚ) * A_seq n 3 - (Z_seq n : ℚ) * A_seq n 2 := by
  have h1 : A_seq n n * (Nat.factorial (n - 1) : ℚ) / 2 = (n - 2 : ℚ) * A_seq n 3 - (Z_seq n : ℚ) * A_seq n 2 := A_seq_n n hn
  have h2 : A_seq n n = 4 := by delta Z_seq and A_seq at*
                                rw[WellFounded.Nat.fix_eq, dif_pos (by constructor)]
  exact h1▸h2▸by ring

def X_int (n k : ℕ) : ℤ := (Nat.factorial (k - 1) : ℤ) * A_int n k

lemma A_int_rec (n k : ℕ) (hk : k + 2 ≤ n) :
  A_int n k = (k : ℤ) * A_int n (k + 1) - (k + 1 : ℤ) * A_int n (k + 2) := by
  have h1 : ¬(k ≥ n) := by omega
  have h2 : ¬(k = n - 1) := by omega
  conv => lhs; rw [A_int]
  simp [h1, h2]

lemma X_int_rec (n k : ℕ) (hk : 1 ≤ k) (hk2 : k + 2 ≤ n) :
  X_int n (k + 2) = (k : ℤ) * (X_int n (k + 1) - X_int n k) := by
  have hA := A_int_rec n k hk2
  have h_fact_k : (Nat.factorial k : ℤ) = (k : ℤ) * (Nat.factorial (k - 1) : ℤ) := by induction↑hk with constructor
  have h_fact_kp1 : (Nat.factorial (k + 1) : ℤ) = (k + 1 : ℤ) * (Nat.factorial k : ℤ) := by constructor
  unfold X_int
  exact (by assumption▸h_fact_k.symm▸ (hA)▸by·ring!)

def Y_int (n k : ℕ) : ℤ := (k - 1 : ℤ) * X_int n k - (k - 2 : ℤ) * X_int n (k + 1)

lemma Y_int_rec (n k : ℕ) (hk : 1 ≤ k) (hk2 : k + 2 ≤ n) :
  Y_int n (k + 1) = (k : ℤ) * Y_int n k := by
  unfold Y_int
  have hX := X_int_rec n k hk hk2
  cases@isEmpty_or_nonempty ℝ
  · norm_num at‹_›
  simp_all![X_int]
  ring

lemma Y_int_eq_fact_aux (n i : ℕ) (hkn : 2 + i ≤ n - 1) :
  Y_int n (2 + i) = (Nat.factorial (2 + i - 1) : ℤ) * Y_int n 2 := by
  induction i with
  | zero =>
    have h1 : 2 + 0 - 1 = 1 := rfl
    have h2 : (Nat.factorial 1 : ℤ) = 1 := rfl
    have h3 : Y_int n (2 + 0) = Y_int n 2 := rfl
    rw [h1, h2, h3]
    ring
  | succ i ih =>
    have h_le : 2 + i ≤ n - 1 := by omega
    have h_ih := ih h_le
    have hk1 : 1 ≤ 2 + i := by omega
    have hk2 : 2 + i + 2 ≤ n := by omega
    have h_rec := Y_int_rec n (2 + i) hk1 hk2
    have h_step : Y_int n (2 + (i + 1)) = (2 + i : ℤ) * Y_int n (2 + i) := by
      have heq : 2 + (i + 1) = 2 + i + 1 := by omega
      rw [heq]
      exact h_rec
    rw [h_step, h_ih]
    have h_fact : (Nat.factorial (2 + (i + 1) - 1) : ℤ) = (2 + i : ℤ) * (Nat.factorial (2 + i - 1) : ℤ) := by
      have heq_n : 2 + (i + 1) - 1 = i + 2 := by omega
      have heq_n_minus : 2 + i - 1 = i + 1 := by omega
      rw [heq_n, heq_n_minus]
      have hf : Nat.factorial (i + 2) = (i + 2) * Nat.factorial (i + 1) := rfl
      rw [hf]
      push_cast
      have h_alg : (i + 2 : ℤ) = (2 + i : ℤ) := by omega
      rw [h_alg]
    rw [h_fact]
    ring

lemma Y_int_eq_fact (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n - 1) :
  Y_int n k = (Nat.factorial (k - 1) : ℤ) * Y_int n 2 := by
  have h_k : ∃ i : ℕ, k = 2 + i := ⟨k - 2, by omega⟩
  rcases h_k with ⟨i, rfl⟩
  exact Y_int_eq_fact_aux n i hkn

lemma A_int_n (n : ℕ) : A_int n n = 4 := by
  have h1 : n ≥ n := by omega
  unfold A_int
  simp

lemma X_int_n (n : ℕ) (hn : n ≥ 3) : X_int n n = (Nat.factorial (n - 1) : ℤ) * 4 := by
  unfold X_int
  rw [A_int_n n]

lemma Y_int_two_eq_A_int (n : ℕ) : Y_int n 2 = A_int n 2 := by
  unfold Y_int X_int
  have h1 : (2 - 1 : ℤ) = 1 := rfl
  have h2 : (2 - 2 : ℤ) = 0 := rfl
  have h3 : (Nat.factorial (2 - 1) : ℤ) = 1 := rfl
  ring

lemma A_int_two_eq (n : ℕ) (hn : n ≥ 3) : (A_int n 2 : ℚ) = (n : ℚ)^2 + 2 * (n : ℚ) - 4 := by
  rw [← A_int_eq n 2]
  exact A2_eq n hn

lemma A_int_two_pos (n : ℕ) (hn : n ≥ 3) : A_int n 2 > 0 := by
  have h1 := A_int_two_eq n hn
  exact_mod_cast h1▸sub_pos.mpr <|mod_cast (by valid ∘(2).one_le_pow n) (by valid)

lemma Y_int_pos (n k : ℕ) (hn : n ≥ 3) (hk : 2 ≤ k) (hkn : k ≤ n - 1) : Y_int n k > 0 := by
  have h1 : Y_int n k = (Nat.factorial (k - 1) : ℤ) * Y_int n 2 := Y_int_eq_fact n k hk hkn
  have h2 : Y_int n 2 = A_int n 2 := Y_int_two_eq_A_int n
  rw [h2] at h1
  have h3 := A_int_two_pos n hn
  have h4 : (Nat.factorial (k - 1) : ℤ) > 0 := by exact_mod_cast Nat.factorial_pos (k - 1)
  rw [h1]
  positivity

lemma X_int_pos_d (n d : ℕ) (hn : n ≥ 3) (hd : d ≤ n - 2) : X_int n (n - d) > 0 := by
  induction d with
  | zero =>
    have hX := X_int_n n hn
    have h3 : (Nat.factorial (n - 1) : ℤ) > 0 := by exact_mod_cast Nat.factorial_pos (n - 1)
    have h_eq : n - 0 = n := by omega
    rw [h_eq]
    rw [hX]
    positivity
  | succ d ih =>
    have hd_le : d ≤ n - 2 := by omega
    have h_ih := ih hd_le
    set k := n - d - 1
    have hk : 2 ≤ k := by omega
    have hkn : k ≤ n - 1 := by omega
    have hY_pos := Y_int_pos n k hn hk hkn
    have hY_def : Y_int n k = (k - 1 : ℤ) * X_int n k - (k - 2 : ℤ) * X_int n (k + 1) := rfl
    have hk_eq : n - d = k + 1 := by omega
    have h_ih_k : X_int n (k + 1) > 0 := by
      rw [← hk_eq]
      exact h_ih
    have h_k1 : (k - 1 : ℤ) > 0 := by omega
    have h_k2 : (k - 2 : ℤ) ≥ 0 := by omega
    have h_Xk : (k - 1 : ℤ) * X_int n k = Y_int n k + (k - 2 : ℤ) * X_int n (k + 1) := by
      rw [hY_def]
      ring
    have h_rhs_pos : Y_int n k + (k - 2 : ℤ) * X_int n (k + 1) > 0 := by
      have : (k - 2 : ℤ) * X_int n (k + 1) ≥ 0 := mul_nonneg h_k2 (le_of_lt h_ih_k)
      linarith
    have h_lhs_pos : (k - 1 : ℤ) * X_int n k > 0 := by linarith
    have h_eq : n - (d + 1) = k := by omega
    rw [h_eq]
    nlinarith

lemma A_int_pos (n k : ℕ) (hn : n ≥ 3) (hk : 2 ≤ k) (hkn : k ≤ n) : A_int n k > 0 := by
  have hd : n - k ≤ n - 2 := by omega
  have hX_pos := X_int_pos_d n (n - k) hn hd
  have h_eq : n - (n - k) = k := by omega
  rw [h_eq] at hX_pos
  have hX_def : X_int n k = (Nat.factorial (k - 1) : ℤ) * A_int n k := rfl
  have h_fact : (Nat.factorial (k - 1) : ℤ) > 0 := by exact_mod_cast Nat.factorial_pos (k - 1)
  rw [hX_def] at hX_pos
  nlinarith

lemma A_seq_neq_zero (n k : ℕ) (hn : n ≥ 3) (hk : 2 ≤ k) (hkn : k ≤ n) : A_seq n k ≠ 0 := by
  have h_int_pos : A_int n k > 0 := A_int_pos n k hn hk hkn
  have h_int_neq_0 : A_int n k ≠ 0 := ne_of_gt h_int_pos
  have h_eq := A_int_eq n k
  rw [h_eq]
  exact_mod_cast h_int_neq_0

lemma frac_sub_eq (k A1 A2 : ℚ) (h : A1 ≠ 0) : k - (k + 1) * A2 / A1 = (k * A1 - (k + 1) * A2) / A1 := by
  have h1 : k = k * A1 / A1 := by rw [mul_div_cancel_right₀ k h]
  nth_rw 1 [h1]
  rw [←sub_div]

lemma cf_denom_eq_A_seq_d (d : ℕ) : ∀ n k : ℕ, n - k = d → n > 2 → 2 ≤ k → k ≤ n - 1 →
    continued_fraction_denominator n k = A_seq n k / A_seq n (k + 1) := by
  induction d with
  | zero =>
    intro n k hd hn hk hk2
    omega
  | succ d ih =>
    intro n k hd hn hk hk2
    unfold continued_fraction_denominator
    split
    · omega
    · split
      · split
        · have heq1 : k = n - 1 := by omega
          rw [heq1]
          have heq_add : n - 1 + 1 = n := by omega
          rw [heq_add]
          have han : A_seq n n = 4 := by
            unfold A_seq; split; rfl; omega
          have han1 : A_seq n (n - 1) = 5 * (n : ℚ) - 4 := by
            unfold A_seq; split; omega; split; rfl; omega
          rw [han, han1]
          have h_cast : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := Nat.cast_sub (by omega)
          rw [h_cast]
          ring
        · have h_k_lt : k < n - 1 := by omega
          have hd_prev : n - (k + 1) = d := by omega
          have h_rec := ih n (k + 1) hd_prev hn (by omega) (by omega)
          rw [h_rec]
          have hk2_le : k + 2 ≤ n := by omega
          have hA := A_seq_rec n k hk2_le
          rw [hA]
          dsimp only
          have heq2 : k + 1 + 1 = k + 2 := by omega
          rw [heq2]
          have h_div : (k + 1 : ℚ) / (A_seq n (k + 1) / A_seq n (k + 2)) = (k + 1 : ℚ) * A_seq n (k + 2) / A_seq n (k + 1) := by
            rw [div_div_eq_mul_div]
          rw [h_div]
          have hn3 : n ≥ 3 := by omega
          have hk1 : k + 1 ≤ n := by omega
          have hd1 : A_seq n (k + 1) ≠ 0 := A_seq_neq_zero n (k + 1) hn3 (by omega) hk1
          have h_goal := frac_sub_eq (k : ℚ) (A_seq n (k + 1)) (A_seq n (k + 2)) hd1
          rw [h_goal]
      · omega

lemma cf_denom_eq_A_seq (n : ℕ) (k : ℕ) (hn : n > 2) (hk : 2 ≤ k) (hk2 : k ≤ n - 1) :
    continued_fraction_denominator n k = A_seq n k / A_seq n (k + 1) := by
  exact cf_denom_eq_A_seq_d (n - k) n k rfl hn hk hk2
lemma exists_sq_eq_five (p : ℕ) (hp : p.Prime) (hmod : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) :
  ∃ x : ℕ, x ≤ p / 2 ∧ (x : ℤ)^2 ≡ 5 [ZMOD p] := by
  convert (by_contra fun and=>absurd (Fact.mk hp) fun and=>absurd (Fact.mk Nat.prime_five) fun and=> if I:IsSquare (p:ZMod 05) then(? _)else _)
  · rw [ (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one)]at I
    · use‹¬_› (I.elim fun a s=> if I:_ then (by use a.val, I,by simp_all[<-ZMod.intCast_eq_intCast_iff,sq])else (by use p-a.val,by valid,by simp_all[a.val_le,<-ZMod.intCast_eq_intCast_iff,sq]))
    · constructor
    · use (by cases · with ·contradiction)
  · induction hmod with exact I (ZMod.natCast_mod _ _▸ (by assumption :).of_dvd (by decide :5 ∣10)▸by decide)

lemma A_int_two_eq_Z (n : ℕ) (hn : n ≥ 3) : A_int n 2 = (n : ℤ)^2 + 2 * (n : ℤ) - 4 := by
  have h := A_int_two_eq n hn
  exact_mod_cast h

lemma Rat_num_natAbs_eq (a b : ℤ) (hb : b ≠ 0) :
  ((a : ℚ) / (b : ℚ)).num.natAbs = a.natAbs / Int.gcd a b := by
  norm_num[div_eq_mul_inv, Rat.mul_num]at*
  exact (Int.natAbs_ediv_of_dvd (Int.natCast_dvd.2 (by simp_all[Nat.gcd_dvd]))).trans (by cases Ne.lt_or_gt hb with simp_all[b.sign_eq_neg_one_of_neg,b.sign_eq_one_of_pos,Int.gcd])

lemma A363347_eq_reduced (n : ℕ) (hn : n ≥ 3) :
  A363347 n = (A_int n 2).natAbs / Int.gcd (A_int n 2) (A_int n 3) := by
  unfold A363347
  have h1 : ¬(n ≤ 2) := by omega
  simp [h1]
  have hk1 : 2 ≤ 2 := by omega
  have hk2 : 2 ≤ n - 1 := by omega
  have h_cf := cf_denom_eq_A_seq n 2 (by omega) hk1 hk2
  rw [h_cf]
  have hA2 : A_seq n 2 = (A_int n 2 : ℚ) := A_int_eq n 2
  have hA3 : A_seq n 3 = (A_int n 3 : ℚ) := A_int_eq n 3
  rw [hA2, hA3]
  have hn3 : (A_int n 3 : ℚ) ≠ 0 := by
    have h_pos : A_int n 3 > 0 := A_int_pos n 3 hn (by omega) (by omega)
    exact_mod_cast ne_of_gt h_pos
  exact Rat_num_natAbs_eq (A_int n 2) (A_int n 3) (by exact_mod_cast hn3)

lemma A_int_3_2_bound (n : ℕ) (hn : n ≥ 3) :
  2 * (Nat.factorial (n - 1) : ℤ) = (n - 2 : ℤ) * A_int n 3 - Z_seq n * A_int n 2 := by
  have h := A_seq_3_2_bound n hn
  have hA2 : A_seq n 2 = A_int n 2 := A_int_eq n 2
  have hA3 : A_seq n 3 = A_int n 3 := A_int_eq n 3
  rw [hA2, hA3] at h
  exact_mod_cast h

def S_val (n : ℕ) : ℤ :=
  if n ≤ 3 then 0
  else S_val (n - 1) + (Nat.factorial (n - 4) : ℤ)
termination_by n

lemma S_val_rec (m : ℕ) (hm : 3 ≤ m) : S_val (m + 1) = S_val m + (Nat.factorial (m - 3) : ℤ) := by
  conv => lhs; unfold S_val
  split
  · omega
  · have h_eq1 : m + 1 - 1 = m := by omega
    have h_eq2 : m + 1 - 4 = m - 3 := by omega
    rw [h_eq1, h_eq2]

lemma X_3_form_k_base (n : ℕ) (h_n : 3 ≤ n) :
  2 * (3 - 2 : ℤ) * A_int n 3 = (3 - 2 : ℤ) * S_val 3 * A_int n 2 + X_int n 3 := by
  unfold S_val X_int
  split
  · have h_fact : (Nat.factorial (3 - 1) : ℤ) = 2 := rfl
    rw [h_fact]
    ring
  · omega

lemma X_3_form_k_step (n m : ℕ) (hm : 3 ≤ m) (h_n_succ : m + 1 ≤ n)
  (ih : 2 * (m - 2 : ℤ) * A_int n 3 = (m - 2 : ℤ) * S_val m * A_int n 2 + X_int n m) :
  2 * (m + 1 - 2 : ℤ) * A_int n 3 = (m + 1 - 2 : ℤ) * S_val (m + 1) * A_int n 2 + X_int n (m + 1) := by
  have hm2 : 2 ≤ m := by omega
  have hm_le : m ≤ n - 1 := by omega
  have hY_def : Y_int n m = (m - 1 : ℤ) * X_int n m - (m - 2 : ℤ) * X_int n (m + 1) := rfl
  have hY_val : Y_int n m = (Nat.factorial (m - 1) : ℤ) * Y_int n 2 := Y_int_eq_fact n m hm2 hm_le
  have hY2 : Y_int n 2 = A_int n 2 := Y_int_two_eq_A_int n
  have hS_rec : S_val (m + 1) = S_val m + (Nat.factorial (m - 3) : ℤ) := S_val_rec m hm
  have h_fact : (Nat.factorial (m - 1) : ℤ) = (m - 1 : ℤ) * (m - 2 : ℤ) * (Nat.factorial (m - 3) : ℤ) := by
    have h1 : m - 1 = m - 2 + 1 := by omega
    have h2 : m - 2 = m - 3 + 1 := by omega
    have h_fact1 : Nat.factorial (m - 1) = (m - 1) * Nat.factorial (m - 2) := by
      rw [h1]; exact Nat.factorial_succ (m - 2)
    have h_fact2 : Nat.factorial (m - 2) = (m - 2) * Nat.factorial (m - 3) := by
      rw [h2]; exact Nat.factorial_succ (m - 3)
    rw [h_fact1, h_fact2]
    have hc1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
    have hc2 : ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 := by omega
    push_cast
    rw [hc1, hc2]
    ring
  have h_alg : (m - 2 : ℤ) * (2 * (m + 1 - 2 : ℤ) * A_int n 3) = (m - 2 : ℤ) * ((m + 1 - 2 : ℤ) * S_val (m + 1) * A_int n 2 + X_int n (m + 1)) := by
    calc
      (m - 2 : ℤ) * (2 * (m + 1 - 2 : ℤ) * A_int n 3) = (m + 1 - 2 : ℤ) * (2 * (m - 2 : ℤ) * A_int n 3) := by ring
      _ = (m + 1 - 2 : ℤ) * ((m - 2 : ℤ) * S_val m * A_int n 2 + X_int n m) := by rw [ih]
      _ = (m + 1 - 2 : ℤ) * (m - 2 : ℤ) * S_val m * A_int n 2 + (m + 1 - 2 : ℤ) * X_int n m := by ring
      _ = (m - 1 : ℤ) * (m - 2 : ℤ) * S_val m * A_int n 2 + (m - 1 : ℤ) * X_int n m := by
        have h_eq : (m + 1 - 2 : ℤ) = (m - 1 : ℤ) := by omega
        rw [h_eq]
      _ = (m - 1 : ℤ) * (m - 2 : ℤ) * S_val m * A_int n 2 + (Y_int n m + (m - 2 : ℤ) * X_int n (m + 1)) := by
        have h_Y : (m - 1 : ℤ) * X_int n m = Y_int n m + (m - 2 : ℤ) * X_int n (m + 1) := by linarith
        rw [h_Y]
      _ = (m - 1 : ℤ) * (m - 2 : ℤ) * S_val m * A_int n 2 + ((Nat.factorial (m - 1) : ℤ) * A_int n 2 + (m - 2 : ℤ) * X_int n (m + 1)) := by
        rw [hY_val, hY2]
      _ = (m - 1 : ℤ) * (m - 2 : ℤ) * S_val m * A_int n 2 + ((m - 1 : ℤ) * (m - 2 : ℤ) * (Nat.factorial (m - 3) : ℤ) * A_int n 2 + (m - 2 : ℤ) * X_int n (m + 1)) := by
        rw [h_fact]
      _ = (m - 2 : ℤ) * ((m - 1 : ℤ) * (S_val m + (Nat.factorial (m - 3) : ℤ)) * A_int n 2 + X_int n (m + 1)) := by ring
      _ = (m - 2 : ℤ) * ((m - 1 : ℤ) * S_val (m + 1) * A_int n 2 + X_int n (m + 1)) := by rw [← hS_rec]
      _ = (m - 2 : ℤ) * ((m + 1 - 2 : ℤ) * S_val (m + 1) * A_int n 2 + X_int n (m + 1)) := by
        have h_eq : (m - 1 : ℤ) = (m + 1 - 2 : ℤ) := by omega
        rw [h_eq]
  have h_m_neq : (m - 2 : ℤ) ≠ 0 := by omega
  exact mul_left_cancel₀ h_m_neq h_alg

lemma X_3_form_k (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n) :
  2 * (k - 2 : ℤ) * A_int n 3 = (k - 2 : ℤ) * S_val k * A_int n 2 + X_int n k := by
  have h_cases : ∃ i : ℕ, k = 3 + i := ⟨k - 3, by omega⟩
  rcases h_cases with ⟨i, hi⟩
  subst hi
  induction i with
  | zero =>
    have h_n : 3 ≤ n := by omega
    exact X_3_form_k_base n h_n
  | succ i ih =>
    have hm : 3 ≤ 3 + i := by omega
    have h_n_succ : 3 + i + 1 ≤ n := by omega
    have h_ih := ih (by omega) (by omega)
    exact X_3_form_k_step n (3 + i) hm h_n_succ h_ih

lemma A_3_eq_n (n : ℕ) (hn : n ≥ 4) :
  2 * (n - 2 : ℤ) * A_int n 3 = (n - 2 : ℤ) * S_val n * A_int n 2 + (Nat.factorial (n - 1) : ℤ) * 4 := by
  have hk : 3 ≤ n := by omega
  have hkn : n ≤ n := by omega
  have h_form := X_3_form_k n n hk hkn
  have hXn := X_int_n n (by omega)
  rw [hXn] at h_form
  exact h_form

lemma A_3_eq_from_n (n : ℕ) (h : 2 * (n - 2 : ℤ) * A_int n 3 = (n - 2 : ℤ) * S_val n * A_int n 2 + (Nat.factorial (n - 1) : ℤ) * 4)
  (h_fact : (Nat.factorial (n - 1) : ℤ) = (n - 1 : ℤ) * (n - 2 : ℤ) * (Nat.factorial (n - 3) : ℤ))
  (hd : (n - 2 : ℤ) ≠ 0) :
  2 * A_int n 3 = S_val n * A_int n 2 + 4 * (n - 1 : ℤ) * (Nat.factorial (n - 3) : ℤ) := by
  rw [h_fact] at h
  have h_alg : (n - 2 : ℤ) * (2 * A_int n 3) = (n - 2 : ℤ) * (S_val n * A_int n 2 + 4 * (n - 1 : ℤ) * (Nat.factorial (n - 3) : ℤ)) := by
    calc
      (n - 2 : ℤ) * (2 * A_int n 3) = 2 * (n - 2 : ℤ) * A_int n 3 := by ring
      _ = (n - 2 : ℤ) * S_val n * A_int n 2 + (n - 1 : ℤ) * (n - 2 : ℤ) * (Nat.factorial (n - 3) : ℤ) * 4 := h
      _ = (n - 2 : ℤ) * (S_val n * A_int n 2 + 4 * (n - 1 : ℤ) * (Nat.factorial (n - 3) : ℤ)) := by ring
  exact mul_left_cancel₀ hd h_alg

lemma fact_n_minus_one (n : ℕ) (hn : n ≥ 4) :
  (Nat.factorial (n - 1) : ℤ) = (n - 1 : ℤ) * (n - 2 : ℤ) * (Nat.factorial (n - 3) : ℤ) := by
  have h1 : n - 1 = n - 2 + 1 := by omega
  have h2 : n - 2 = n - 3 + 1 := by omega
  have h_fact1 : Nat.factorial (n - 1) = (n - 1) * Nat.factorial (n - 2) := by
    rw [h1]
    exact Nat.factorial_succ (n - 2)
  have h_fact2 : Nat.factorial (n - 2) = (n - 2) * Nat.factorial (n - 3) := by
    rw [h2]
    exact Nat.factorial_succ (n - 3)
  rw [h_fact1, h_fact2]
  have hc1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have hc2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  push_cast
  rw [hc1, hc2]
  ring

lemma A_3_eq (n : ℕ) (hn : n ≥ 4) :
  2 * A_int n 3 = S_val n * A_int n 2 + 4 * (n - 1 : ℤ) * (Nat.factorial (n - 3) : ℤ) := by
  apply A_3_eq_from_n n
  · apply A_3_eq_n
    omega
  · exact fact_n_minus_one n hn
  · omega

lemma S_val_even (n : ℕ) (hn : n ≥ 5) : ∃ m : ℤ, S_val n = 2 * m := by
  have h_cases : ∃ i : ℕ, n = 5 + i := ⟨n - 5, by omega⟩
  rcases h_cases with ⟨i, hi⟩
  subst hi
  clear hn
  induction i with
  | zero =>
    have hs : S_val 5 = S_val 4 + (Nat.factorial 1 : ℤ) := S_val_rec 4 (by omega)
    have hs4 : S_val 4 = S_val 3 + (Nat.factorial 0 : ℤ) := S_val_rec 3 (by omega)
    have hs3 : S_val 3 = 0 := by
      unfold S_val
      split
      · rfl
      · omega
    have h_val : S_val 5 = 2 := by
      rw [hs, hs4, hs3]
      rfl
    use 1
    rw [h_val]
    ring
  | succ i ih =>
    have hs_rec : S_val (5 + i + 1) = S_val (5 + i) + (Nat.factorial (5 + i - 3) : ℤ) := S_val_rec (5 + i) (by omega)
    rcases ih with ⟨m, hm⟩
    have h_fact_even : ∃ k : ℤ, (Nat.factorial (5 + i - 3) : ℤ) = 2 * k := by
      have h_fact : 2 ∣ Nat.factorial (5 + i - 3) := Nat.dvd_factorial (by omega) (by omega)
      rcases h_fact with ⟨k_nat, hk⟩
      use k_nat
      exact_mod_cast hk
    rcases h_fact_even with ⟨k, hk⟩
    use m + k
    have h_eq : 5 + (i + 1) = 5 + i + 1 := by omega
    rw [h_eq]
    rw [hs_rec, hm, hk]
    ring

lemma k_dvd_term (n k p : ℕ) (hn : n ≥ 5) (hn_lt : 2 * n < p)
  (h_eq : n^2 + 2 * n - 4 = k * p) : (k : ℤ) ∣ 2 * (n - 1 : ℤ) * (Nat.factorial (n - 3) : ℤ) := by
  exact (k.dvd_factorial (by cases k with omega) (k.le_sub_of_add_le (by nlinarith only[hn_lt,h_eq▸Nat.sub_add_cancel (by valid),hn]))).natCast.mul_left _

lemma A_3_exact_from_eq (n : ℕ) (m : ℤ) (h_even : S_val n = 2 * m)
  (h_eq : 2 * A_int n 3 = S_val n * A_int n 2 + 4 * (n - 1 : ℤ) * (Nat.factorial (n - 3) : ℤ)) :
  A_int n 3 = m * A_int n 2 + 2 * (n - 1 : ℤ) * (Nat.factorial (n - 3) : ℤ) := by
  rw [h_even] at h_eq
  linarith

lemma A_3_exact (n : ℕ) (hn : n ≥ 5) :
  ∃ m : ℤ, A_int n 3 = m * A_int n 2 + 2 * (n - 1 : ℤ) * (Nat.factorial (n - 3) : ℤ) := by
  have h_even : ∃ m : ℤ, S_val n = 2 * m := by
    apply S_val_even
    omega
  rcases h_even with ⟨m, hm⟩
  use m
  apply A_3_exact_from_eq n m hm
  apply A_3_eq
  omega

lemma k_dvd_A3_from_formula (n k p : ℕ) (hn : n ≥ 5) (h_eq : (A_int n 2).natAbs = k * p)
  (h_exact : ∃ m : ℤ, A_int n 3 = m * A_int n 2 + 2 * (n - 1 : ℤ) * (Nat.factorial (n - 3) : ℤ))
  (h_term : (k : ℤ) ∣ 2 * (n - 1 : ℤ) * (Nat.factorial (n - 3) : ℤ)) : (k : ℤ) ∣ A_int n 3 := by
  rcases h_exact with ⟨m, hm⟩
  have h_A2_dvd : (k : ℤ) ∣ A_int n 2 := by
    have hk_dvd : k ∣ (A_int n 2).natAbs := by rw [h_eq]; exact dvd_mul_right k p
    exact_mod_cast Int.dvd_natAbs.mp (by exact_mod_cast hk_dvd)
  rw [hm]
  exact dvd_add (dvd_mul_of_dvd_right h_A2_dvd m) h_term

lemma A_int_two_abs_eq (n : ℕ) (hn : n ≥ 5) :
  ((n : ℤ)^2 + 2 * (n : ℤ) - 4).natAbs = n^2 + 2 * n - 4 := by
  have hn_pos : (n : ℤ)^2 + 2 * (n : ℤ) - 4 ≥ 0 := by nlinarith
  have h3 : n^2 + 2 * n ≥ 4 := by nlinarith
  have h_eq : ((n : ℤ)^2 + 2 * (n : ℤ) - 4) = ((n^2 + 2 * n - 4 : ℕ) : ℤ) := by
    rw [Nat.cast_sub h3]
    push_cast
    ring
  rw [h_eq]
  rfl

lemma k_dvd_A3 (n k p : ℕ) (hp : p.Prime) (hn : n ≥ 3) (hn_lt : 2 * n < p)
  (h_eq : (A_int n 2).natAbs = k * p) : (k : ℤ) ∣ A_int n 3 := by
  have h_cases : n = 3 ∨ n = 4 ∨ n ≥ 5 := by omega
  rcases h_cases with rfl | rfl | hn5
  · simp_all[A_int]
    norm_num [by_contra (by decide ∘(h_eq▸Nat.mul_le_mul.comp k.two_le_iff.mpr ⟨ fun and=>by simp_all,.⟩ hn_lt))]
  · simp_all![Nat.eq_zero_of_dvd_of_lt (h_eq▸dvd_mul_left _ _) ∘hn_lt.trans']
    simp_all![A_int]
    match k with|0|1|2=>norm_num[<-h_eq▸p.mul_div_cancel_left]at* | S+3=>exact absurd (h_eq▸add_mul S _ _) (by valid)
  · have h_A2 : A_int n 2 = (n : ℤ)^2 + 2 * (n : ℤ) - 4 := A_int_two_eq_Z n (by omega)
    have h_abs : ((n : ℤ)^2 + 2 * (n : ℤ) - 4).natAbs = n^2 + 2 * n - 4 := A_int_two_abs_eq n hn5
    have h_eq_nat : n^2 + 2 * n - 4 = k * p := by
      rw [← h_abs]
      rw [← h_A2]
      exact h_eq
    apply k_dvd_A3_from_formula n k p hn5 h_eq
    · apply A_3_exact
      omega
    · apply k_dvd_term n k p hn5 hn_lt h_eq_nat

lemma p_not_dvd_A3 (n p k : ℕ) (hp : p.Prime) (hn : n ≥ 3) (hn_lt : n < p)
  (h_eq : (A_int n 2).natAbs = k * p) : ¬ ((p : ℤ) ∣ A_int n 3) := by
  intro h_div
  have h_bound := A_int_3_2_bound n hn
  have h_p_dvd_A2 : (p : ℤ) ∣ A_int n 2 := by
    have h_nat : p ∣ (A_int n 2).natAbs := by
      rw [h_eq]
      exact dvd_mul_left p k
    have h_nat_Z : (p : ℤ) ∣ ((A_int n 2).natAbs : ℤ) := by exact_mod_cast h_nat
    exact Int.dvd_natAbs.mp h_nat_Z
  have h_p_dvd_rhs : (p : ℤ) ∣ (n - 2 : ℤ) * A_int n 3 - Z_seq n * A_int n 2 := by
    apply Int.dvd_sub
    · exact dvd_mul_of_dvd_right h_div (n - 2 : ℤ)
    · exact dvd_mul_of_dvd_right h_p_dvd_A2 (Z_seq n)
  have h_p_dvd_lhs : (p : ℤ) ∣ 2 * (Nat.factorial (n - 1) : ℤ) := by
    rw [← h_bound] at h_p_dvd_rhs
    exact h_p_dvd_rhs
  have h_p_dvd_fact : (p : ℤ) ∣ (Nat.factorial (n - 1) : ℤ) := by
    have hp_prime : Prime (p : ℤ) := by exact_mod_cast Nat.prime_iff_prime_int.mp hp
    rcases Prime.dvd_or_dvd hp_prime h_p_dvd_lhs with h2 | hfact
    · exfalso
      have h_le : p ≤ 2 := by exact_mod_cast Int.le_of_dvd (by decide) h2
      omega
    · exact hfact
  have h_p_dvd_fact_nat : p ∣ Nat.factorial (n - 1) := by exact_mod_cast h_p_dvd_fact
  have h_le := (Nat.Prime.dvd_factorial hp).mp h_p_dvd_fact_nat
  omega

lemma A363347_eval (n p k : ℕ) (hp : p.Prime) (hn : n ≥ 3) (hn_lt : n < p)
  (h_A2 : (A_int n 2).natAbs = k * p) (hk_pos : k > 0)
  (h_k_dvd : (k : ℤ) ∣ A_int n 3) (h_p_not_dvd : ¬ ((p : ℤ) ∣ A_int n 3)) : A363347 n = p := by
  have h_reduced := A363347_eq_reduced n hn
  rw [h_reduced]
  rw [h_A2]
  have h_gcd : Int.gcd (A_int n 2) (A_int n 3) = k := by
    simp_all only [Int.gcd, false, (hp.coprime_iff_not_dvd.mpr (by assumption ∘Int.natCast_dvd.mpr.comp ( ·.trans (Nat.gcd_dvd_right _ _)))).gcd_mul_right_cancel, false,Int.natCast_dvd]
    rwa [ (hp.coprime_iff_not_dvd.mpr (by assumption)).gcd_mul_right_cancel,Nat.gcd_eq_left]
  have h_gcd_nat : (Int.gcd (A_int n 2) (A_int n 3) : ℕ) = k := by exact_mod_cast h_gcd
  rw [h_gcd_nat]
  exact Nat.mul_div_cancel_left p hk_pos

lemma A363347_achieves_prime (p : ℕ) (hp : p.Prime) (hmod : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) :
  ∃ n : ℕ, A363347 n = p := by
  have h_p_ge_11 : p ≥ 11 := by match p with |1|9|10=>contradiction | S +11=>omega
  have hx := exists_sq_eq_five p hp hmod
  rcases hx with ⟨x, hx_le, hx_sq⟩
  have hx_ge_4 : x ≥ 4 := by match x with|0|1|2|3=>use absurd (p.le_of_dvd · (Int.natCast_dvd.1 hx_sq.dvd)) (by valid) | n+4=>omega
  use x - 1
  have hn_ge_3 : x - 1 ≥ 3 := by exact (3).le_pred_of_lt (by valid)
  have hn_lt : x - 1 < p := by first|omega
  have h_eq : ((x - 1 : ℕ) : ℤ)^2 + 2 * ((x - 1 : ℕ) : ℤ) - 4 ≡ 0 [ZMOD p] := by apply (hx_sq.symm.dvd.trans ⟨(1),.trans (by rw [Nat.cast_pred (by valid)]) (by {ring})⟩).modEq_zero_int
  have h_A2_eq : A_int (x - 1) 2 = ((x - 1 : ℕ) : ℤ)^2 + 2 * ((x - 1 : ℕ) : ℤ) - 4 := A_int_two_eq_Z (x - 1) hn_ge_3
  have h_A2_mod : (A_int (x - 1) 2) ≡ 0 [ZMOD p] := by
    rw [h_A2_eq]
    exact h_eq
  have h_k : ∃ k : ℕ, (A_int (x - 1) 2).natAbs = k * p := by exact ⟨ _, (p.div_mul_cancel ((Int.natCast_dvd.mp (Int.dvd_of_emod_eq_zero (by assumption))))).symm⟩
  rcases h_k with ⟨k, hk_eq⟩
  have hk_pos : k > 0 := by exact (k).pos_of_mul_pos_right ↑(hk_eq▸Int.natAbs_pos.2 (by exact(@h_A2_eq▸sub_ne_zero.mpr ((mod_cast (by valid))))))
  have hn_lt2 : 2 * (x - 1) < p := by ((((omega))))
  have h_k_dvd := k_dvd_A3 (x - 1) k p hp hn_ge_3 hn_lt2 hk_eq
  have h_p_not_dvd := p_not_dvd_A3 (x - 1) p k hp hn_ge_3 hn_lt hk_eq
  exact A363347_eval (x - 1) p k hp hn_ge_3 hn_lt hk_eq hk_pos h_k_dvd h_p_not_dvd
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : ∀ p : ℕ, (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) → ∃ n : ℕ, A363347 n = p := by
  -- EVOLVE-BLOCK-START
  intro p hp
  exact A363347_achieves_prime p hp.1 hp.2
  -- EVOLVE-BLOCK-END
