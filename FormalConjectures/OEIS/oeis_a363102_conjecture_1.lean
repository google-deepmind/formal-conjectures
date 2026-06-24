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




open Nat Finset

/--
Auxiliary sequence A051403, defined as
$$\frac{(n+2) \sum_{k=0}^n k!}{2}$$
-/
def a051403 (n : ℕ) : ℕ :=
  let fact_sum := Finset.sum (range (n + 1)) (fun k => k.factorial)
  ((n + 2) * fact_sum) / 2

/--
A363102: Denominator of the continued fraction $1/(2-3/(3-4/(4-5/(...(n-1)-n/(-2)))))$.
The sequence is defined by the formula:
$$a(n) = \frac{n^2 - 2}{\gcd(n^2 - 2, 2 \cdot A051403(n-3) + n \cdot A051403(n-4))}$$
The formula is valid for $n \ge 3$.
-/
def a (n : ℕ) : ℕ :=
  let num : ℕ := n ^ 2 - 2
  let a051403_nm3 := a051403 (n - 3)
  let a051403_nm4 := a051403 (n - 4)
  let denom_arg := 2 * a051403_nm3 + n * a051403_nm4
  -- The subtraction n^2 - 2 is safe for n >= 3.
  num / Nat.gcd num denom_arg

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
-- You can put your definitions and lemmas here.
lemma D_n_eq (n : ℕ) (h : 4 ≤ n) :
  2 * (2 * a051403 (n - 3) + n * a051403 (n - 4)) =
  (n^2 - 2) * (Finset.sum (range (n - 3)) (fun k => k.factorial)) + 2 * (n - 1) * (n - 3).factorial := by
  push_cast[a051403,mul_assoc,←Int.ofNat_inj,((Nat.pow_le_pow_left h _)).trans', (by valid:n-3=n-4+1)]
  rw [Nat.cast_sub h, Nat.cast_pred (by valid), Finset.sum_range_succ, mul_add, mul_left_comm 2]
  refine h.eq_or_lt.elim (by bound) fun and=>.trans (congr_arg₂ _ ((congr_arg _) ↑(Int.mul_ediv_cancel' ?_)) (.trans (mul_left_comm _ _ _) (congr_arg _ ((Int.mul_ediv_cancel') ?_)))) (by ring)
  · refine if a:_ then(.mul_right a _)else .mul_left ? _ _
    exact (.add (mod_cast(1).le_induction (by decide) ( fun and A B=> Finset.sum_range_succ (.!) _▸B.add ((2).factorial_dvd_factorial (by valid))) _ (tsub_pos_of_lt and)) (mod_cast(2).factorial_dvd_factorial (by valid)))
  · exact (Int.ofNat_sub h▸.mul_left ↑(mod_cast(1).le_induction (by decide) ( fun and A B=> Finset.sum_range_succ (.!) _▸B.add ((2).factorial_dvd_factorial (by valid))) _ (tsub_pos_of_lt and)) _)

lemma gcd_2Dn (n : ℕ) (h : 4 ≤ n) :
  Nat.gcd (n^2 - 2) (2 * (2 * a051403 (n - 3) + n * a051403 (n - 4))) =
  Nat.gcd (n^2 - 2) (2 * (n - 1) * (n - 3).factorial) := by
  delta a051403
  obtain ⟨n, rfl⟩:=Nat.exists_eq_add_of_le' h
  simp_all![mul_assoc, mul_add,add_sq,mul_left_comm, Finset.sum_range_succ _ (n + 1)]
  rewrite [Nat.mul_div_cancel']
  · rw [←mul_left_comm (n+4),Nat.mul_div_cancel']
    · exact (congr_arg _ (by ring)).trans (Nat.gcd_add_mul_left_right _ _<|∑ a ∈_, _)
    · match n with|0|1=> decide | S+2=>exact (.mul_left ↑( S.rec (by decide) fun and x =>( Finset.sum_range_succ _ _).symm.subst (x.add ((2).factorial_dvd_factorial (by push_cast)))) _)
  · match n with|0|1=> decide | S+2=>simp_all[(2).dvd_iff_mod_eq_zero, Finset.sum_nat_mod, Finset.sum_range_succ',Nat.add_mod,Nat.mul_mod,Nat.mod_eq_zero_of_dvd ∘Nat.dvd_factorial _,]

lemma gcd_2Y (n : ℕ) (h : 4 ≤ n) :
  Nat.gcd (n^2 - 2) (2 * (n - 1) * (n - 3).factorial) =
  Nat.gcd (n^2 - 2) (2 * (n - 1).factorial) := by
  refine match(n) with | S+3 =>mul_assoc (2) _ _▸.symm ↑?_
  simp_all![add_sq, true,mul_left_comm]
  norm_num[(by ring:S^2+2* S*3+7=(S+1)*(S+5)+(2))]
  obtain ⟨k, rfl⟩| ⟨a, rfl⟩:= S.even_or_odd
  · exact (Nat.Coprime.gcd_mul_left_cancel_right _) (by norm_num[parity_simps])
  norm_num[show (2 *a+2) * (2*a+6)+2=2*(2*(a+1)*(a+3)+1)by ring,Nat.gcd_mul_left,mul_assoc,mul_left_comm _ 2]
  exact (Nat.Coprime.gcd_mul_left_cancel_right _) (by·norm_num[←(2).mul_succ, false, ←mul_assoc])

lemma S_even (n : ℕ) (h : 5 ≤ n) :
  2 ∣ Finset.sum (range (n - 3)) (fun k => k.factorial) := by
  exact (2).le_induction (by decide) ( fun and a s=> Finset.sum_range_succ (.!) and▸s.add ((2).factorial_dvd_factorial a)) _<|Nat.le_sub_of_add_le h

lemma gcd_D_Y (n : ℕ) (h : 5 ≤ n) :
  Nat.gcd (n^2 - 2) (2 * a051403 (n - 3) + n * a051403 (n - 4)) =
  Nat.gcd (n^2 - 2) ((n - 1) * (n - 3).factorial) := by
  have h4 : 4 ≤ n := by
    omega
  have h_D_eq := D_n_eq n h4
  have h_S_even := S_even n h
  exact (h_S_even.elim fun and x =>mul_left_cancel₀ (by decide) (h_D_eq.trans (by rw [x,mul_assoc, mul_left_comm, mul_add]))▸Nat.gcd_mul_left_add_right _ _ _)

lemma gcd_Y_C (n : ℕ) (h : 5 ≤ n) :
  Nat.gcd (n^2 - 2) ((n - 1) * (n - 3).factorial) =
  Nat.gcd (n^2 - 2) (n - 1).factorial := by
  refine(n).sub_add_cancel (by valid:(n)≥3)▸Nat.gcd_eq_iff.mpr (@? _)
  simp_all![Nat.gcd_dvd,Nat.dvd_gcd_iff]
  use(Nat.factorization_le_iff_dvd (Nat.gcd_ne_zero_right (by positivity)) (by positivity)).1 fun and=>? _, fun and A B=>B.trans ⟨_+1,by ring⟩
  simp_all[mul_left_commn /mul_zero, false,_root_.add_sq, false,_root_.Nat.succ_sub_succ_eq_sub _,_root_.Nat.sub_eq_zero_iff_le, false,_root_.Nat.factorization_gcd, false,_root_.Nat.factorial_ne_zero, zero_dvd_iff]
  use or_iff_not_imp_right.2 fun and' => if a:_ then((((congr_arg _) ↑(Nat.factorization_def _ a)).ge.trans') ? _)else by simp_all
  obtain ⟨@c⟩ :=eq_or_ne and 2
  · obtain ⟨a, _⟩| ⟨a, _⟩:=(n-3).even_or_odd
    · simp_all [ ←two_mul,Nat.factorization_eq_zero_of_not_dvd]
    simp_all![padicValNat.mul, mul_pow, mul_add, add_assoc,add_sq,Nat.factorization,Nat.factorial_ne_zero]
    norm_num[padicValNat.mul, add_mul,padicValNat.eq_zero_of_not_dvd ( ((2).dvd_add_right ⟨a, rfl⟩).not.mpr _),padicValNat_factorial_mul,←mul_assoc]
    ring
    exact (not_lt.1 (by cases (pow_dvd_pow _) · |>.trans (pow_padicValNat_dvd) with valid)).trans (by valid: 1 ≤ _)
  · use(Nat.factorization_eq_zero_of_not_dvd (by valid ∘ (and.prime_dvd_prime_iff_eq a (by decide)).1 ∘or_self_iff.1 ∘a.dvd_mul.1 ∘? _)).trans_le bot_le
    simp_all[←CharP.cast_eq_zero_iff (ZMod and),Nat.factorization_eq_zero_iff,<-eq_sub_iff_add_eq]
    use (by linear_combination.*2)

lemma gcd_D_n (n : ℕ) (h : 5 ≤ n) :
  Nat.gcd (n^2 - 2) (2 * a051403 (n - 3) + n * a051403 (n - 4)) =
  Nat.gcd (n^2 - 2) (n - 1).factorial := by
  have h1 := gcd_D_Y n h
  have h2 := gcd_Y_C n h
  focus valid

lemma a_simplified (n : ℕ) (h : 5 ≤ n) :
  a n = (n^2 - 2) / Nat.gcd (n^2 - 2) (n - 1).factorial := by
  unfold a
  have h_gcd := gcd_D_n n h
  hint

lemma test_padic (n p : ℕ) (hp : Nat.Prime p) :
  p ^ (padicValNat p n) ∣ n := by
  apply↑pow_padicValNat_dvd

lemma padic_div_gcd (a b p : ℕ) (hp : Nat.Prime p) (ha : a ≠ 0) (hb : b ≠ 0) (h : p ∣ a / Nat.gcd a b) :
  padicValNat p a > padicValNat p b := by
  simp_all[a.gcd_dvd _,a.factorization_gcd, true,hp.dvd_iff_one_le_factorization (a.div_gcd_pos_of_pos_left _ _).ne',Nat.factorization_def _,pos_iff_ne_zero]
  omega

lemma prime_le_fac (n p : ℕ) (hp : Nat.Prime p) (h : p ≤ n) :
  p ∣ n.factorial := by
  exact (hp).dvd_factorial.mpr h

lemma p_pow_div_M (n p : ℕ) (h5 : 5 ≤ n) (hp : Nat.Prime p) (hdiv : p ∣ (n^2 - 2) / Nat.gcd (n^2 - 2) (n - 1).factorial) :
  p ^ ((n - 1) / p + 1) ∣ n^2 - 2 := by
  refine if a:_=0 then⟨0, a⟩else(((pow_succ _ _)).dvd.trans (mul_dvd_mul_right.comp (hp.pow_dvd_iff_le_factorization ↑(Nat.gcd_ne_zero_left a)).mpr ↑? _ _)).trans.comp (Nat.mul_dvd_of_dvd_div ↑(gcd_dvd_left _ _)) (hdiv)
  simp_all[hp.dvd_iff_one_le_factorization (Nat.div_gcd_pos_of_pos_left _ _).ne',Nat.gcd_dvd,Nat.factorization_gcd,Nat.factorization_def,pos_iff_ne_zero,Nat.factorial_ne_zero]
  refine (by_contra (absurd (Fact.mk hp) fun and=>. ( (and_self_iff.2 (.trans (? _) (padicValNat_factorial (Nat.le_succ _)).ge)).imp_left (by valid))))
  push_cast[pow_one,le_add_self, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ']

lemma p_pow_bound (n p : ℕ) (hp : 2 ≤ p) (h2 : 2 * p ≤ n - 1) (hdiv : p ^ ((n - 1) / p + 1) ∣ n^2 - 2) :
  n ≤ 29 := by
  use not_lt.1 fun and=>match n with | S+1=>Nat.not_dvd_of_pos_of_lt ((2).sub_pos_of_lt ((2).lt_pow_self (by valid))) ((Nat.sub_le _ _).trans_lt ? _) hdiv
  obtain ⟨A, B⟩ := hp.eq_or_lt
  · exact (pow_le_pow_left' (by valid: S+1≤2*(S/2 + 1)) (2)).trans_lt ((14).le_induction (by decide) ( fun and A B=>pow_succ (2) _▸by linarith! only[A, B, mul_le_mul_left' A and]) _ (by valid: S/2≥14))
  rcases eq_or_ne (S/p : ℕ) (2)
  · refine (by assumption:).symm▸pow_succ p (2)▸by nlinarith only[pow_three p, and,‹_›▸p.lt_mul_div_succ S (by valid)]
  rcases eq_or_ne (S/p : ℕ) (3)
  · refine (by assumption▸pow_succ p (3)▸by (nlinarith only[p.div_lt_iff_lt_mul (by valid) |>.mp ((by assumption:).trans_lt (by constructor)),pow_three (p-3 : ℤ), and]))
  apply(Nat.pow_lt_pow_left (S.succ_lt_succ (p.lt_mul_div_succ S (by valid))) two_ne_zero).trans_le
  cases eq_or_ne (S/p) 1
  · linarith![ (p.le_div_iff_mul_le (by valid)).mpr h2]
  norm_num[pow_add]at h2⊢
  cases eq_or_ne (S/p : ℕ) (4)
  · use (by valid▸by match p with|3|4=>omega | S+5=>nlinarith only [pow_three (S* S)])
  · refine(5).le_induction (by nlinarith [pow_three (p^2-9 : ℤ)]) ( fun and A B=>pow_succ p and▸by nlinarith [mul_le_mul_left' hp and]) @_ (by match p.div_pos (by valid: S≥ _) with | S=>omega: S/p≥5)

lemma c_eq_two_helper (n p c : ℕ) (h1 : n^2 - 2 = c * p^2) (h2 : n - 1 ≤ 2 * p) (h3 : p < n) (hn : 30 ≤ n) : c = 2 := by
  use (by_contra fun and=>absurd (h1▸Nat.sub_add_cancel ((2).lt_pow_self (by valid)).le) fun and=> if a:c≤4 then(? _)else (by nlinarith[tsub_le_iff_left.1 h2]))
  match c with|0|1=>nlinarith|3|4=>_
  · use absurd (n.pow_mod (2) _) (by match P:n%3 with|0|1|2 | S+3=>omega)
  · cases pow_dvd_pow_of_dvd.comp (Nat.prime_two).dvd_of_dvd_pow (and.subst (by valid)) (2) with valid

lemma gcd_2p_sq (n p : ℕ) (h1 : n^2 - 2 = 2 * p^2) (hp : Nat.Prime p) (h2 : n - 1 ≤ 2 * p) (h3 : p < n) (hn : 30 ≤ n) :
  Nat.gcd (2 * p^2) (n - 1).factorial = 2 * p := by
  cases (p.dvd_factorial hp.pos (p.le_sub_one_of_lt @h3))
  obtain ⟨x, rfl⟩| ⟨a, rfl⟩:=‹ℕ›.even_or_odd
  · simp_all[p.gcd_mul_left,mul_comm p,←two_mul,←mul_assoc,Nat.sub_eq_iff_eq_add ((2).lt_pow_self (hn.trans' ↑_)).le,sq]
    rw[Nat.gcd_mul_right,Nat.gcd_mul_left,hp.coprime_iff_not_dvd.mpr fun and=>absurd (congr_arg (@ ·.factorization p) (‹_ = _› :)) ? _,mul_one]
    norm_num [hp, right_ne_zero_of_mul ↑( left_ne_zero_of_mul (by convert← (n-1).factorial_ne_zero)),hp.ne_zero,Nat.factorization_def _ _]
    apply (by_contra ↑(absurd (Fact.mk hp) fun and=>. ( (padicValNat_factorial (Nat.le_succ _)).trans_ne _) ) )
    norm_num[*,hp.ne_one,(Nat.div_eq_of_lt_le (by valid) ((tsub_lt_iff_right h3.pos).2 (by nlinarith[h1▸le_tsub_add])):(n-1)/p=1), Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ']
    exact ( Finset.sum_eq_zero fun and b=>Nat.div_eq_of_lt ((p.mul_le_pow hp.ne_one _).trans' (by nlinarith[h1▸le_tsub_add,n.sub_le (1)]))).trans_ne (Ne.symm fun and=>by simp_all[hp.ne_one])
  · induction(@Nat.prime_two).dvd_mul.mp ((‹_›▸Nat.dvd_factorial (by decide) ) (by valid)) with apply absurd hp.eq_two_or_odd (by valid)

lemma p_sq_div_M (n p : ℕ) (h5 : 5 ≤ n) (hp : Nat.Prime p) (hpn : p < n)
  (hdiv : p ∣ (n^2 - 2) / Nat.gcd (n^2 - 2) (n - 1).factorial) :
  p^2 ∣ n^2 - 2 := by
  simp_all only[p.dvd_div_iff_mul_dvd,sq, mul_dvd_mul,p.dvd_gcd,hp.dvd_factorial,p.le_sub_one_of_lt,Nat.gcd_dvd]
  exact (mul_dvd_mul_right (p.dvd_gcd ↑(dvd_of_mul_left_dvd hdiv) (hp.dvd_factorial.mpr hpn.le_pred ) ) p).trans hdiv

lemma p_cube_div_M (n p : ℕ) (h5 : 5 ≤ n) (hp : Nat.Prime p) (hpn : 2 * p ≤ n - 1)
  (hdiv : p ∣ (n^2 - 2) / Nat.gcd (n^2 - 2) (n - 1).factorial) :
  p^3 ∣ n^2 - 2 := by
  simp_all only[p.dvd_div_iff_mul_dvd, two_mul,Nat.gcd_dvd,pow_three']
  refine if a:_=0 then⟨0,a⟩else((mul_dvd_mul_right ↑(Nat.dvd_gcd @(? _) ↑(.trans (?_) (Nat.factorial_mul_factorial_dvd_factorial hpn)))) p).trans hdiv
  · exact (mul_dvd_mul_right (p.dvd_gcd ↑(dvd_of_mul_left_dvd hdiv) (hp.dvd_factorial.mpr (by valid))) p).trans hdiv
  · apply((mul_dvd_mul (hp.dvd_factorial.mpr (by constructor)) (hp.dvd_factorial.mpr (by constructor) )).trans (p.factorial_mul_factorial_dvd_factorial_add p)).mul_right

set_option maxRecDepth 100000
lemma a_small_eval (n : ℕ) (hn : 5 ≤ n) (h_lt : n < 30) : a n = 1 ∨ Nat.Prime (a n) := by
  rw [a_simplified n hn]
  interval_cases n <;> decide

lemma a_small_34 (n : ℕ) (hn : 3 ≤ n) (h_lt : n < 5) : a n = 1 ∨ Nat.Prime (a n) := by
  interval_cases n <;> decide

lemma R_n_not_composite (n : ℕ) (hn : 30 ≤ n) :
  let R := (n^2 - 2) / Nat.gcd (n^2 - 2) (n - 1).factorial
  R = 1 ∨ Nat.Prime R := by
  intro R
  by_cases hR : R = 1
  · exact Or.inl hR
  · apply Or.inr
    by_contra hPrime
    have hR_neq_1 : R ≠ 1 := hR
    have hR_pos : 0 < R := by
      exact (Nat.div_gcd_pos_of_pos_left _) ↑(tsub_pos_of_lt ((Nat.pow_le_pow_left @hn (2)).trans' (by decide)))
    let p := R.minFac
    have hp_prime : Nat.Prime p := Nat.minFac_prime hR_neq_1
    have hp_div_R : p ∣ R := Nat.minFac_dvd R
    have hp_sq_le_R : p^2 ≤ R := Nat.minFac_sq_le_self hR_pos hPrime
    have hR_le : R ≤ n^2 - 2 := by
      apply Nat.div_le_self
    have hp_sq_le : p^2 ≤ n^2 - 2 := le_trans hp_sq_le_R hR_le
    have hp_lt_n : p < n := by
      refine (p.pow_lt_pow_iff_left two_ne_zero).1 (by. (omega))
    have h5 : 5 ≤ n := by omega
    have hp_sq_div : p^2 ∣ n^2 - 2 := p_sq_div_M n p h5 hp_prime hp_lt_n hp_div_R
    by_cases h_case1 : 2 * p ≤ n - 1
    · have hp_pow_div : p ^ ((n - 1) / p + 1) ∣ n^2 - 2 := p_pow_div_M n p h5 hp_prime hp_div_R
      have hn_le_29 : n ≤ 29 := p_pow_bound n p hp_prime.two_le h_case1 hp_pow_div
      omega
    · have h2 : n - 1 ≤ 2 * p := by omega
      have hp_sq_pos : 0 < p^2 := Nat.pos_of_ne_zero (pow_ne_zero 2 hp_prime.ne_zero)
      let c := (n^2 - 2) / p^2
      have hc_eq : n^2 - 2 = c * p^2 := (Nat.div_mul_cancel hp_sq_div).symm
      have hc2 : c = 2 := c_eq_two_helper n p c hc_eq h2 hp_lt_n hn
      have hn2_eq : n^2 - 2 = 2 * p^2 := by rw [hc2] at hc_eq; exact hc_eq
      have h_gcd : Nat.gcd (2 * p^2) (n - 1).factorial = 2 * p := gcd_2p_sq n p hn2_eq hp_prime h2 hp_lt_n hn
      have hR_eq_p : R = p := by
        dsimp [R]
        rw [hn2_eq, h_gcd]
        have h_p_pos : 0 < p := Nat.pos_of_ne_zero hp_prime.ne_zero
        have h_2_pos : 0 < 2 := by decide
        have h_2p_pos : 0 < 2 * p := Nat.mul_pos h_2_pos h_p_pos
        have h_pow : 2 * p^2 = 2 * p * p := by ring
        rw [h_pow]
        exact Nat.mul_div_cancel_left p h_2p_pos
      exact hPrime (hR_eq_p.symm ▸ hp_prime)

-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : ∀ n : ℕ, 3 ≤ n → a n = 1 ∨ Nat.Prime (a n) := by
  -- EVOLVE-BLOCK-START
  intros n hn
  by_cases h_lt : n < 30
  · by_cases h5 : 5 ≤ n
    · exact a_small_eval n h5 h_lt
    · exact a_small_34 n hn (by omega)
  · have h30 : 30 ≤ n := by omega
    have h5 : 5 ≤ n := by omega
    rw [a_simplified n h5]
    exact R_n_not_composite n h30
  -- EVOLVE-BLOCK-END
