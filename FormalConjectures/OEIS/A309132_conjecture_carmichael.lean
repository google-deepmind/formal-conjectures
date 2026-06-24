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
A309132: a(n) is the denominator of F(n) = A027641(n-1)/n + A027642(n-1)/n^2.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let n_q : ℚ := n
    let B_nm1 : ℚ := bernoulli (n - 1)
    let F_n : ℚ := (B_nm1.num : ℚ) / n_q + (B_nm1.den : ℚ) / (n_q * n_q)
    F_n.den

/-- Definition of a Carmichael number $n$: a composite number s.t. $b^{n-1} \equiv 1 \pmod n$ for all $b$ coprime to $n$. -/
def is_carmichael_number (n : ℕ) : Prop :=
  (¬ Nat.Prime n ∧ n > 1) ∧ (∀ b : ℕ, Nat.gcd b n = 1 → b ^ (n - 1) ≡ 1 [MOD n])

/-- Helper definition for "composite number" -/
def is_composite (n : ℕ) : Prop := ¬ Nat.Prime n ∧ n > 1

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
lemma vsc_sum_range_pow (q m : ℕ) :
  ∑ k ∈ Finset.range q, (k : ℚ) ^ m =
    ∑ i ∈ Finset.range m, _root_.bernoulli i * ((m + 1).choose i : ℚ) * (q : ℚ) ^ (m + 1 - i) / (m + 1 : ℚ) +
    _root_.bernoulli m * q := by replace α :=sum_range_pow
                                 exact (α _ _).trans (.trans ( Finset.sum_range_succ _ _) ((congr_arg _) ((div_eq_iff (by norm_cast)).2 (by norm_num[m.add_sub_cancel_left,mul_right_comm]))))

lemma vsc_sum_val_dvd (q m : ℕ) (hq : q.Prime) (hm : Even m) (hm0 : m ≠ 0) (h : q - 1 ∣ m) :
  padicValRat q (∑ k ∈ Finset.range q, (k : ℚ) ^ m) = 0 := by change(padicValRat q) (∑ a ∈ _,Nat.cast _ ^ _)=0
                                                              norm_cast0
                                                              use match q with|0=>by ·contradiction | S+1=>padicValNat.eq_zero_of_not_dvd (h.elim fun and x =>mt (·.trans (by rw [x, Finset.sum_range_succ'])) fun and' => absurd (Fact.mk hq) ? _)
                                                              use fun and=> if a : ∀ a ∈ Finset.range S,(a+1:ZMod (S + 1))^S=1 then(? _)else a fun a s=>ZMod.pow_card_sub_one_eq_one (mod_cast (by cases.▸ZMod.val_cast_of_lt (a.succ_lt_succ (List.mem_range.1 s))))
                                                              simp_all[pow_mul,←CharP.cast_eq_zero_iff (ZMod (S+1)), ( (ZMod.isUnit_iff_coprime _ _).2 _).ne_zero]

lemma vsc_sum_val_not_dvd (q m : ℕ) (hq : q.Prime) (hm : Even m) (hm0 : m ≠ 0) (h : ¬(q - 1 ∣ m)) :
  padicValRat q (∑ k ∈ Finset.range q, (k : ℚ) ^ m) ≥ 1 := by replace h : q ∣∑ a ∈.range q, a^m := by_contra ( absurd (Fact.mk (@hq) ) fun and=>(@IsCyclic.exists_generator (ZMod q)ˣ _ _).elim fun and x =>. (match q with|0=>by contradiction | S+1=>?_) )
                                                              · exact (mod_cast not_lt.mp (by·norm_num [hq.ne_one,mt (Finset.sum_eq_zero_iff.1 · (1)),hq.one_lt,h]))
                                                              have:and.1^m≠1:=Units.ext_iff.not.1<|by rwa[←orderOf_dvd_iff_pow_eq_one,orderOf_eq_card_of_forall_mem_zpowers x,Nat.card_eq_fintype_card,ZMod.card_units]
                                                              exact (CharP.cast_eq_zero_iff _ _ _).1.comp (Nat.cast_sum _ _).trans (.trans ( Finset.sum_range _) ↑(eq_zero_of_mul_eq_self_left this (( Finset.mul_sum _ _ _).trans ↑( Fintype.sum_equiv (and.mulLeft) _ _ ↑(by simp_all![mul_pow])))))

lemma vsc_term_val (q m i : ℕ) (hq : q.Prime) (hm : Even m) (hi : i < m)
  (hind : padicValRat q (_root_.bernoulli i) ≥ -1)
  (h_nz : _root_.bernoulli i ≠ 0) :
  padicValRat q (_root_.bernoulli i * ((m + 1).choose i : ℚ) * (q : ℚ) ^ (m + 1 - i) / (m + 1 : ℚ)) ≥ 1 := by simp_all[padicValRat.mul,padicValRat.div,padicValRat.pow,hq.ne_zero,Nat.cast_add_one_ne_zero _,Fact.mk,le_add_right hi.le,Nat.choose_eq_zero_iff]
                                                                                                              use match i with|0=>?_ | S+1=>le_sub_comm.1 (mod_cast Nat.choose_succ_right _ _ m.succ_pos▸by_contra fun and=>absurd (m.succ_mul_choose_eq S) ? _)
                                                                                                              · norm_num[le_sub_iff_add_le',(mod_cast Nat.factorization_def _ hq▸Nat.le_of_lt_succ (Nat.factorization_lt _ _):padicValRat q (m+1)≤ m)]
                                                                                                              apply_fun(·.factorization q)
                                                                                                              simp_all![Int.subNatNat_of_le ∘hi.le.trans, S.le_of_lt hi.le, true,m.choose_eq_zero_iff,Nat.factorization_def]
                                                                                                              obtain ⟨@c⟩ :=hq.two_le.eq_or_lt
                                                                                                              · use absurd (padicValNat.eq_zero_of_not_dvd (hm.elim (by valid):¬2 ∣m + 1))<|absurd and ∘ fun and=> (by valid : ¬_+(padicValNat _ _ : ℤ)+_≤ _)
                                                                                                              obtain ⟨k, rfl⟩:=Nat.exists_eq_add_of_le hi.le
                                                                                                              use fun and=>absurd ((S+1+k+1).ordProj_dvd q) fun and=>absurd ((S+1).ordProj_dvd q) ?_
                                                                                                              simp_all[parity_simps,Nat.factorization, add_assoc]
                                                                                                              use fun and' =>absurd ((q.mul_le_pow · (padicValNat q (S+(1+ (k + 1))))|>.trans (Nat.le_of_dvd k.succ_pos ((Nat.dvd_add_right ((pow_dvd_pow q ?_).trans and')).1 (S.add_assoc _ _▸and))))) ?_
                                                                                                              · use not_lt.1 fun andx=>absurd ((q.mul_le_pow · _|>.trans (Nat.le_of_dvd (by valid) ((Nat.dvd_sub ((pow_dvd_pow q (andx.le)).trans and) and'))))) fun and20=>?_
                                                                                                                refine absurd ((3).mul_le_mul_right (padicValNat q (S + 1)) ‹q>2›) ( absurd @‹_+(padicValNat _ _+_ : ℤ) ≤_› ∘by valid)
                                                                                                              · use absurd ‹_+(padicValNat _ _+_ : ℤ) ≤_› ∘by valid ∘ ((3).mul_le_mul_right _ ‹_›).trans.comp (. hq.ne_one)

lemma padic_val_sum_ge_one_of_terms {S : Finset ℕ} {f : ℕ → ℚ}
  (q : ℕ) (hq : q.Prime)
  (h_val : ∀ i ∈ S, f i = 0 ∨ padicValRat q (f i) ≥ 1) :
  ∑ i ∈ S, f i = 0 ∨ padicValRat q (∑ i ∈ S, f i) ≥ 1 := by use or_iff_not_imp_left.2 (S.induction (nofun) (fun A B R M=>? _) h_val)
                                                            use fun and=>by cases em (f A=0) with cases em (B.sum f=0) with simp_all[padicValRat.min_le_padicValRat_add _|>.trans',Fact.mk, (and _ _).resolve_left]

lemma vsc_sum_terms_val (q m : ℕ) (hq : q.Prime) (hm : Even m)
  (hind : ∀ i < m, _root_.bernoulli i ≠ 0 → padicValRat q (_root_.bernoulli i) ≥ -1) :
  (∑ i ∈ Finset.range m, _root_.bernoulli i * ((m + 1).choose i : ℚ) * (q : ℚ) ^ (m + 1 - i) / (m + 1 : ℚ)) = 0 ∨
  padicValRat q (∑ i ∈ Finset.range m, _root_.bernoulli i * ((m + 1).choose i : ℚ) * (q : ℚ) ^ (m + 1 - i) / (m + 1 : ℚ)) ≥ 1 := by
  let f := fun i => _root_.bernoulli i * ((m + 1).choose i : ℚ) * (q : ℚ) ^ (m + 1 - i) / (m + 1 : ℚ)
  have h_val : ∀ i ∈ Finset.range m, f i = 0 ∨ padicValRat q (f i) ≥ 1 := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases h_nz : _root_.bernoulli i = 0
    · left
      dsimp [f]
      rw [h_nz]
      ring
    · right
      dsimp [f]
      have hind_i := hind i hi h_nz
      exact vsc_term_val q m i hq hm hi hind_i h_nz
  exact padic_val_sum_ge_one_of_terms q hq h_val

lemma padic_val_bernoulli_0 (q : ℕ) (hq : q.Prime) :
  padicValRat q (_root_.bernoulli 0) ≥ -1 := by norm_num

lemma padic_val_bernoulli_1 (q : ℕ) (hq : q.Prime) :
  padicValRat q (_root_.bernoulli 1) ≥ -1 := by norm_num[padicValRat, false,padicValInt, false,←Nat.factorization_def _,hq]
                                                apply Finsupp.single_apply.trans_le (by (bound))

lemma padic_val_bernoulli_odd (q i : ℕ) (hq : q.Prime) (hi : Odd i) (hi1 : i > 1) :
  _root_.bernoulli i = 0 := by rwa[bernoulli_eq_bernoulli'_of_ne_one hi1.ne',bernoulli'_odd_eq_zero hi]

lemma padic_val_sum_int_ge_zero (q m : ℕ) (hq : q.Prime) :
  (∑ k ∈ Finset.range q, (k : ℚ) ^ m) = 0 ∨
  padicValRat q (∑ k ∈ Finset.range q, (k : ℚ) ^ m) ≥ 0 := by refine or_iff_not_imp_left.mpr fun and=> ((congr_arg _) (by norm_cast)).ge.trans'.comp (padicValRat.of_nat).symm.subst (by constructor)

lemma padic_val_ge_minus_one_of_eq (q : ℕ) (hq : q.Prime) (S R B : ℚ)
  (heq : S = R + B * q)
  (hS : S = 0 ∨ padicValRat q S ≥ 0)
  (hR : R = 0 ∨ padicValRat q R ≥ 0)
  (hB_nz : B ≠ 0) :
  padicValRat q B ≥ -1 := by use neg_le_iff_add_nonneg.2 (not_lt.1 fun and=>absurd (Fact.mk hq) fun and=> if a : R=0 then(? _)else if I: S=0 then(? _)else@? _)
                             · simp_all[padicValRat.mul, not_le.2,hq.ne_zero]
                             · norm_num[padicValRat.mul, not_le.mpr, add_eq_zero_iff_eq_neg.mp (heq▸I),hq.ne_zero, *] at hR
                             simp_all[padicValRat.add_eq_of_lt, not_le.2,padicValRat.mul,hq.ne_zero,add_comm R]
                             norm_num[padicValRat.add_eq_of_lt, not_le.2,padicValRat.mul,Fact.mk,hq.ne_zero,hR.trans_lt', *] at hS

lemma vsc_padic_val_bernoulli_ge_minus_one (q m : ℕ) (hq : q.Prime) (h_nz : _root_.bernoulli m ≠ 0) :
  padicValRat q (_root_.bernoulli m) ≥ -1 := by
  induction m using Nat.strong_induction_on with
  | h m hind =>
    by_cases hm0 : m = 0
    · rw [hm0]
      exact padic_val_bernoulli_0 q hq
    · by_cases hm1 : m = 1
      · rw [hm1]
        exact padic_val_bernoulli_1 q hq
      · have h_gt_1 : m > 1 := by omega
        by_cases h_odd : Odd m
        · have h_zero := padic_val_bernoulli_odd q m hq h_odd h_gt_1
          contradiction
        · have h_even : Even m := by rwa [←m.not_odd_iff_even]
          have h_sum := vsc_sum_range_pow q m
          have h_S := padic_val_sum_int_ge_zero q m hq
          have h_R_val := vsc_sum_terms_val q m hq h_even hind
          have h_R : (∑ i ∈ Finset.range m, _root_.bernoulli i * ((m + 1).choose i : ℚ) * (q : ℚ) ^ (m + 1 - i) / (m + 1 : ℚ)) = 0 ∨
                     padicValRat q (∑ i ∈ Finset.range m, _root_.bernoulli i * ((m + 1).choose i : ℚ) * (q : ℚ) ^ (m + 1 - i) / (m + 1 : ℚ)) ≥ 0 := by
            rcases h_R_val with h0 | h1
            · exact Or.inl h0
            · have h_pos : padicValRat q (∑ i ∈ Finset.range m, _root_.bernoulli i * ((m + 1).choose i : ℚ) * (q : ℚ) ^ (m + 1 - i) / (m + 1 : ℚ)) ≥ 0 := by exact (le_of_lt) (h1)
              exact Or.inr h_pos
          exact padic_val_ge_minus_one_of_eq q hq (∑ k ∈ Finset.range q, (k : ℚ) ^ m)
            (∑ i ∈ Finset.range m, _root_.bernoulli i * ((m + 1).choose i : ℚ) * (q : ℚ) ^ (m + 1 - i) / (m + 1 : ℚ))
            (_root_.bernoulli m) h_sum h_S h_R h_nz

lemma padic_val_eq_minus_one_of_eq (q : ℕ) (hq : q.Prime) (S R B : ℚ)
  (heq : S = R + B * q)
  (hS : padicValRat q S = 0)
  (hS0 : S ≠ 0)
  (hR : R = 0 ∨ padicValRat q R ≥ 1) :
  padicValRat q B = -1 := by use (by_contra fun and=>absurd (Fact.mk hq) fun and' => if a : R=0 then(? _)else absurd (hS▸heq▸padicValRat.add_eq_min) ? _)
                             · simp_all[padicValRat.mul,←eq_sub_iff_add_eq]
                             norm_num[padicValRat.mul ( fun and=>by simp_all: B≠0),hq.ne_zero]
                             if H: B=0 then{simp_all} else use hS0,a,H, fun and=>by simp_all[padicValRat.mul, add_eq_zero_iff_eq_neg.eq,mt (padicValRat.min_le_padicValRat_add _).trans_eq,hq.ne_zero],by grind

lemma padic_val_ge_zero_of_eq (q : ℕ) (hq : q.Prime) (S R B : ℚ)
  (heq : S = R + B * q)
  (hS : padicValRat q S ≥ 1)
  (hR : R = 0 ∨ padicValRat q R ≥ 1) :
  B = 0 ∨ padicValRat q B ≥ 0 := by use or_iff_not_imp_left.mpr fun and=>not_lt.1 fun and' =>absurd (Fact.mk @hq) fun and=> if a : R=0 then by simp_all[padicValRat.mul, not_le.mpr,hq.ne_zero]else(? _)
                                    rewrite [heq,add_comm _,padicValRat.add_eq_of_lt (by norm_num [·] at hS) (by·norm_num [hq.ne_zero, true, *]) (by norm_num [hq.ne_zero, *])] at hS
                                    · simp_all[padicValRat.mul, two_mul,hq.ne_zero, not_le.2 and']
                                    · norm_num[padicValRat.mul, false, (hR.resolve_left a).trans_lt',hq.ne_zero, *]

lemma vsc_sum_ne_zero (q m : ℕ) (hq : q.Prime) (hm : Even m) (hm0 : m ≠ 0) :
  ∑ k ∈ Finset.range q, (k : ℚ) ^ m ≠ 0 := by change∑ a ∈ _,(id _) ^m≠0
                                              exact ( Finset.sum_pos' (fun R L=>hm.pow_nonneg _) ⟨1,by norm_num[hq.one_lt]⟩).ne'

lemma vsc_padic_val_bernoulli_dvd (q m : ℕ) (hq : q.Prime) (hm : Even m) (hm0 : m ≠ 0) (h : q - 1 ∣ m) :
  padicValRat q (_root_.bernoulli m) = -1 := by
  have hind : ∀ i < m, _root_.bernoulli i ≠ 0 → padicValRat q (_root_.bernoulli i) ≥ -1 := by
    intro i _ hn
    exact vsc_padic_val_bernoulli_ge_minus_one q i hq hn
  have h_sum := vsc_sum_range_pow q m
  have h_S := vsc_sum_val_dvd q m hq hm hm0 h
  have h_S0 := vsc_sum_ne_zero q m hq hm hm0
  have h_R := vsc_sum_terms_val q m hq hm hind
  exact padic_val_eq_minus_one_of_eq q hq (∑ k ∈ Finset.range q, (k : ℚ) ^ m)
    (∑ i ∈ Finset.range m, _root_.bernoulli i * ((m + 1).choose i : ℚ) * (q : ℚ) ^ (m + 1 - i) / (m + 1 : ℚ))
    (_root_.bernoulli m) h_sum h_S h_S0 h_R

lemma vsc_padic_val_bernoulli_not_dvd (q m : ℕ) (hq : q.Prime) (hm : Even m) (hm0 : m ≠ 0) (h : ¬(q - 1 ∣ m)) :
  padicValRat q (_root_.bernoulli m) ≥ 0 := by
  have hind : ∀ i < m, _root_.bernoulli i ≠ 0 → padicValRat q (_root_.bernoulli i) ≥ -1 := by
    intro i _ hn
    exact vsc_padic_val_bernoulli_ge_minus_one q i hq hn
  have h_sum := vsc_sum_range_pow q m
  have h_S := vsc_sum_val_not_dvd q m hq hm hm0 h
  have h_R := vsc_sum_terms_val q m hq hm hind
  have h_B_nonneg := padic_val_ge_zero_of_eq q hq (∑ k ∈ Finset.range q, (k : ℚ) ^ m)
    (∑ i ∈ Finset.range m, _root_.bernoulli i * ((m + 1).choose i : ℚ) * (q : ℚ) ^ (m + 1 - i) / (m + 1 : ℚ))
    (_root_.bernoulli m) h_sum h_S h_R
  rcases h_B_nonneg with h_B0 | h_Bpos
  · rw [h_B0]
    norm_num
  · exact h_Bpos

lemma denominator_from_padic (x : ℚ) (S : Finset ℕ)
  (h_primes : ∀ p ∈ S, Nat.Prime p)
  (h_val_in : ∀ p ∈ S, padicValRat p x = -1)
  (h_val_out : ∀ p : ℕ, Nat.Prime p → p ∉ S → padicValRat p x ≥ 0) :
  x.den = ∏ p ∈ S, p := by rw [←Nat.factorization_prod_pow_eq_self ↑x.den_ne_zero, Finsupp.prod_of_support_subset (s:=S)]
                           · simp_all[padicValRat]
                             refine S.prod_congr rfl fun and(A) =>((congr_arg _) ((Nat.factorization_def _ (by tauto)).trans (Nat.cast_injective (sub_right_injective ((h_val_in and A).trans ?_))))).trans (pow_one _)
                             norm_num[padicValInt.eq_zero_of_not_dvd ((h_primes and (A)).coprime_iff_not_dvd.mp (x.reduced.symm.of_dvd_left (by_contra (by valid ∘ (padicValNat.eq_zero_of_not_dvd ·▸(h_val_in and A))))) ∘Int.natCast_dvd.1)]
                           · exact fun and=>by_contra ∘fun R M=>absurd (h_val_out and) (by simp_all-contextual[padicValRat,padicValInt.eq_zero_of_not_dvd ∘mt (x.reduced▸and.dvd_gcd ∘Int.natCast_dvd.1),Nat.Prime.ne_one])
                           · subsingleton

lemma bernoulli_den_vsc (m : ℕ) (hm : Even m) (hm0 : m ≠ 0) :
  (_root_.bernoulli m).den = ∏ p ∈ Finset.filter (fun p => p.Prime ∧ p - 1 ∣ m) (Finset.range (m + 2)), p := by
  apply denominator_from_padic
  · intro p hp
    rw [Finset.mem_filter] at hp
    exact hp.2.1
  · intro p hp
    rw [Finset.mem_filter] at hp
    exact vsc_padic_val_bernoulli_dvd p m hp.2.1 hm hm0 hp.2.2
  · intro p hp hp_not_mem
    by_cases h_div : p - 1 ∣ m
    · have h_mem : p ∈ Finset.filter (fun p => p.Prime ∧ p - 1 ∣ m) (Finset.range (m + 2)) := by
        rw [Finset.mem_filter]
        refine ⟨?_, hp, h_div⟩
        rw [Finset.mem_range]
        refine (by valid ∘Nat.eq_zero_of_dvd_of_lt) (h_div)
      contradiction
    · exact vsc_padic_val_bernoulli_not_dvd p m hp hm hm0 h_div

lemma korselt_criterion (n : ℕ) :
  is_carmichael_number n ↔
  (is_composite n ∧ Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1) := by
  rw[is_carmichael_number, and_comm,is_composite]
  use fun⟨A, B⟩=>⟨B,Nat.squarefree_iff_prime_squarefree.2 fun and p ⟨a, _⟩=>absurd (A (and * a+1)) ? _,fun R M ⟨a, _⟩=>by_contra fun and=>absurd (Fact.mk M) fun and=>?_⟩
  · use fun⟨k,A, B⟩=>⟨fun R M=>n.modEq_of_dvd (n.prod_primeFactors_of_squarefree A▸.trans (Nat.cast_prod _ _).dvd (Finset.prod_dvd_of_coprime (by simp_all[·.coprime_primes]) ?_)),k⟩
    simp_all[←ZMod.intCast_zmod_eq_zero_iff_dvd,n.prod_primeFactors_of_squarefree]
    exact (fun K V a s =>by cases B K V a with ·norm_num [pow_mul,CharP.cast_eq_zero_iff _ K, *, V.coprime_iff_not_dvd.1.comp (.symm) ↑(.of_dvd_right a M),Fact.mk _,ZMod.pow_card_sub_one_eq_one])
  · norm_num[*,mul_assoc,←geom_sum_mul_neg,Nat.coprime_mul_iff_right,Nat.modEq_iff_dvd]at B⊢
    exact (mul_dvd_mul_iff_right (mod_cast (by cases.▸B.2))).not.mpr ↑(mod_cast (p.not_dvd_one ∘ (and.dvd_add_right · |>.mp (by(norm_num [←CharP.cast_eq_zero_iff (ZMod and),le_of_lt B.2])))))
  by_cases h : R.Coprime a
  · have:= ZMod.chineseRemainder h
    use match a with|0=>by valid | S+1=>(@IsCyclic.exists_generator (ZMod R)ˣ _ _).elim fun and p=>absurd (A (this.symm (and, 1)).val) (by valid ∘? _)
    norm_num [Prod.isUnit_iff,←ZMod.eq_iff_modEq_nat, R.totient_prime M,←ZMod.isUnit_iff_coprime,←map_pow,←Units.val_pow_eq_pow_val,←orderOf_dvd_iff_pow_eq_one,orderOf_eq_card_of_forall_mem_zpowers, *]
  · convert (by_contra (h ∘ M.coprime_iff_not_dvd.2)).elim fun and x =>(absurd (A (R*and + 1)) _)
    norm_num[*,Nat.coprime_mul_iff_right, false,←geom_sum_mul_neg, true,Nat.modEq_iff_dvd] at B⊢
    exact (mul_dvd_mul_iff_right (mod_cast (by cases ·▸B.2))).not.mpr (( ZMod.intCast_zmod_eq_zero_iff_dvd _ _).not.mp (by norm_num [le_of_lt B.right]))

lemma a_eq_n_sq_div_gcd (n : ℕ) (hn : n > 0) :
  a n = n^2 / Nat.gcd (Int.natAbs (n * (_root_.bernoulli (n - 1)).num + (_root_.bernoulli (n - 1)).den)) (n^2) := by
  delta and a
  field_simp at *
  simp_all[hn.ne',mul_comm,div_eq_mul_inv,<-inv_pow,Rat.mul_den]
  exact (.trans (by rw [Int.sign_eq_one_of_pos (by valid),one_pow,mul_one]) (by norm_cast))

lemma a_squarefree_implies (n : ℕ) (U : ℤ) (V : ℕ) (hn : n > 0)
    (hVsq : Squarefree V)
    (ha : Squarefree (n^2 / Nat.gcd (Int.natAbs (n * U + V)) (n^2))) :
    Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ∣ V := by
  use n.squarefree_iff_prime_squarefree.2 fun and R M=>R.1 (ha and (sq and▸Nat.dvd_div_of_mul_dvd ?_)), fun and R M=>Int.ofNat_dvd.mp @(? _)
  · apply(( R.coprime_iff_not_dvd.2 (R.1 ∘hVsq and ∘ _)).symm.pow_right _).mul_dvd_of_dvd_of_dvd ↑(gcd_dvd_right _ _) (sq and▸ M.mul_left _)
    use fun and' =>by_contra fun and' =>R.1 (ha and (Nat.dvd_div_of_mul_dvd (sq n▸?_)))
    simp_all[←sq, R.pow_dvd_iff_le_factorization,hn.ne',←Nat.factorization_le_iff_dvd _,Nat.gcd_eq_zero_iff,hVsq.ne_zero]
    simp_all[hn.ne',←Nat.factorization_le_iff_dvd, R.ne_zero,Nat.gcd_eq_zero_iff]
    use (if H:and=. then H▸.trans (Nat.add_le_add_right (?_:_ ≤ 1) _) @(? _)else ? _)
    · use not_lt.1 (mt (pow_dvd_pow and ·|>.trans (.trans (Nat.ordProj_dvd _ _) (Nat.gcd_dvd_left _ _))) (Int.natCast_dvd.not.1 ((dvd_add_right ?_).not.2 (mod_cast(?_)))))
      · apply((pow_dvd_pow and M).trans (n.ordProj_dvd and)).natCast.mul_right
      · use sq and▸R.1 ∘hVsq and
    · exact ( Finsupp.single_eq_same:_=2).symm▸.trans (by decide) (mul_right_mono M)
    · cases em ((n*U)+V=0) with simp_all[hn.ne',Nat.factorization_gcd]
  · refine(dvd_add_right<| M.natCast.mul_right U).1<|Int.natCast_dvd.2 (by_contra (R.1 ∘ha and ∘ fun and=>sq (_: ℕ)▸Nat.dvd_div_of_mul_dvd ?_))
    push_cast[(( R.coprime_iff_not_dvd.2 (and.comp (·.trans (Nat.gcd_dvd_left _ _)))).symm.pow_right _).mul_dvd_of_dvd_of_dvd,pow_dvd_pow_of_dvd M,Nat.gcd_dvd]

lemma a_even_not_squarefree (n : ℕ) (hn : is_composite n) (he : Even n) :
  ¬ Squarefree (a n) := by
  rw[is_composite, even_iff_two_dvd, a,Nat.squarefree_iff_prime_squarefree] at*
  norm_num[bernoulli_eq_bernoulli'_of_ne_one (by match n with | S+3=>nofun:n-1≠1),bernoulli'_odd_eq_zero (Nat.odd_iff.2 (by valid:(n-1) % 2 =1)) (by match n with | S+3=>omega)]at*
  exact ⟨2, (by decide), (mul_dvd_mul he he).trans (by norm_num [←sq,ne_zero_of_lt hn.2])⟩

lemma carmichael_odd (n : ℕ) (h : is_carmichael_number n) : ¬ Even n := by
  induction(id) h
  refine fun ⟨a, _⟩=> absurd (‹∀_, _› (2 *a-1)) ?_
  cases‹_›▸a.two_mul with norm_num [le_of_lt (by tauto), (by match a with | S+2=>nofun: (2 : (ZMod (2 *(a)))) ≠0),←ZMod.eq_iff_modEq_nat, false,Nat.odd_sub _,neg_eq_iff_add_eq_zero]

lemma a_squarefree_of_conditions (n : ℕ) (U : ℤ) (V : ℕ) (hn : n > 0)
    (hsq : Squarefree n)
    (hV : ∀ p : ℕ, p.Prime → p ∣ n → p ∣ V) :
    Squarefree (n^2 / Nat.gcd (Int.natAbs (n * U + V)) (n^2)) := by
  simp_all[hn.ne',sq,n.squarefree_mul_iff,Nat.squarefree_iff_prime_squarefree,Nat.gcd_dvd]
  use@fun A B R=> if a: A ∣n then hsq A B ((mul_dvd_mul_iff_left B.ne_zero).1 ? _)else a (or_self_iff.1 (B.dvd_mul.1 (dvd_of_mul_right_dvd (dvd_of_mul_left_dvd R))))
  obtain ⟨x, rfl⟩:=a
  simp_all only[mul_comm (Nat.gcd _ _), A.dvd_gcd, mul_dvd_mul_iff_left (A.mul_ne_zero B.ne_zero B.ne_zero),push_cast,mul_assoc,dvd_add ⟨_, rfl⟩,dvd_mul_right,←Int.natCast_dvd,Int.ofNat_dvd]
  simp_all only[mul_left_comm x, mul_dvd_mul_iff_left B.ne_zero, or_self,B.dvd_mul]
  induction B.dvd_mul.mp (( A.dvd_gcd (Int.natCast_dvd.mp (.add ⟨_, rfl⟩ (hV A B ⟨x, rfl⟩).natCast) ) ⟨_, rfl⟩).trans R) with assumption

lemma dvd_prod_of_mem (m : ℕ) (p : ℕ) (hp : p ∈ Finset.filter (fun p => p.Prime ∧ p - 1 ∣ m) (Finset.range (m + 2))) :
  p ∣ ∏ p ∈ Finset.filter (fun p => p.Prime ∧ p - 1 ∣ m) (Finset.range (m + 2)), p := by
  exact ( Finset.dvd_prod_of_mem _) hp

lemma mem_filter_of_carmichael_prime (n m p : ℕ) (h : m = n - 1)
  (hn : n > 1) (hp : p.Prime) (hpn : p ∣ n) (hpm : p - 1 ∣ m) :
  p ∈ Finset.filter (fun p => p.Prime ∧ p - 1 ∣ m) (Finset.range (m + 2)) := by
  refine Finset.mem_filter.mpr (by use Finset.mem_range_succ_iff.mpr (h▸by cases@@hn with apply (p.le_of_dvd) (Nat.succ_pos _) hpn ) )

lemma squarefree_prod_primes (m : ℕ) :
  Squarefree (∏ p ∈ Finset.filter (fun p => p.Prime ∧ p - 1 ∣ m) (Finset.range (m + 2)), p) := by
  use @Nat.squarefree_iff_prime_squarefree.2 fun and p=>sq and▸ (p.pow_dvd_iff_le_factorization (Finset.prod_pos fun and β=>(Finset.mem_filter.1 β).2.1.pos).ne').not.2 ?_
  simp_all[ite_le_one _ _|>.trans_lt, Finsupp.single_apply,Nat.factorization_prod,Nat.Prime.ne_zero]
  simp_all[ Finsupp.single_apply,ite_le_one _ _|>.trans_lt, Finset.sum_filter]
  norm_num [ite_le_one _ _ |>.trans_lt, Finset.sum_ite]
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : ∀ (n : ℕ), (is_composite n ∧ Squarefree (a n)) ↔ is_carmichael_number n := by
  -- EVOLVE-BLOCK-START
  intro n
  constructor
  · rintro ⟨hcomp, ha⟩
    have hn_pos : n > 0 := by simp_rw [is_composite, ·>·] at hcomp⊢
                              bound
    by_cases hn_even : Even n
    · have h_not_sq := a_even_not_squarefree n hcomp hn_even
      contradiction
    · have hn_odd : ¬ Even n := hn_even
      have hm_even : Even (n - 1) := by exact (n.not_even_iff_odd.1 (by assumption)).tsub_odd odd_one
      have hm_not_zero : n - 1 ≠ 0 := by match n with | S+2 =>rintro@c
      have hV_eq := bernoulli_den_vsc (n - 1) hm_even hm_not_zero
      have hV_sq : Squarefree (_root_.bernoulli (n - 1)).den := by
        rw [hV_eq]
        exact squarefree_prod_primes (n - 1)
      have ha_eq := a_eq_n_sq_div_gcd n hn_pos
      have ha_sub : Squarefree (n^2 / Nat.gcd (Int.natAbs (n * (_root_.bernoulli (n - 1)).num + (_root_.bernoulli (n - 1)).den)) (n^2)) := by
        convert←ha
      have h_impl := a_squarefree_implies n (_root_.bernoulli (n - 1)).num (_root_.bernoulli (n - 1)).den hn_pos hV_sq ha_sub
      rcases h_impl with ⟨hsq, hV⟩
      rw [korselt_criterion n]
      refine ⟨hcomp, hsq, ?_⟩
      intro p hp hpn
      have hpV := hV p hp hpn
      have hpV_eq : p ∣ ∏ q ∈ Finset.filter (fun q => q.Prime ∧ q - 1 ∣ n - 1) (Finset.range (n - 1 + 2)), q := by
        rwa [ <-hV_eq]
      induction hp.prime.exists_mem_finset_dvd hpV_eq with|intro and a=>push_cast[ (p.prime_dvd_prime_iff_eq _ _).mp a.2, false, Finset.mem_filter.mp (a.1), ↑hp]
  · intro hcarm
    have hcomp : is_composite n := by simp_all[is_composite,is_carmichael_number]
    have hn_odd : ¬ Even n := carmichael_odd n hcarm
    have hn_pos : n > 0 := by match n with|n + 1 =>bound
    have hkorselt : is_composite n ∧ Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1 := by
      simp_all[is_composite,is_carmichael_number]
      use n.squarefree_iff_prime_squarefree.mpr fun and p ⟨a, _⟩ => absurd (hcarm.2 (and * a+1)) ? _,fun R M ⟨a, _⟩ =>by_contra fun and=>absurd (Fact.mk M) fun and=>(@IsCyclic.exists_generator (ZMod R)ˣ _ _).elim @?_
      · norm_num[mul_assoc,←geom_sum_mul_neg,by assumption,Nat.coprime_mul_iff_right, true,Nat.modEq_iff_dvd] at hcarm @hn_pos⊢
        match Fact.mk p with | S=>norm_num[*, mul_dvd_mul_iff_right _,←CharP.intCast_eq_zero_iff (ZMod and),le_of_lt,ne_of_gt]
      by_cases h : R.Coprime a
      · have:= ZMod.chineseRemainder h
        use match a with|0=>by simp_all | S+1 =>fun A B=>absurd (hcarm.2 ( this.symm (A, 1)).val) (by assumption ∘? _)
        norm_num[*, R.totient_prime,←ZMod.eq_iff_modEq_nat,←ZMod.isUnit_iff_coprime,←map_pow,←Units.val_pow_eq_pow_val,←orderOf_dvd_iff_pow_eq_one,orderOf_eq_card_of_forall_mem_zpowers,Prod.isUnit_iff]
      · convert (by_contra (h ∘ M.coprime_iff_not_dvd.2)).elim fun and x =>(absurd (hcarm.2 (R*and + 1)) _)
        norm_num[*,←geom_sum_mul_neg,Nat.coprime_mul_iff_right,Nat.modEq_iff_dvd] at hn_pos⊢
        exact (mul_dvd_mul_iff_right (by cases ↑hn_pos with positivity)).not.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).not.mp (by norm_num[Nat.cast_pred _, *]))
    rcases hkorselt with ⟨_, hsq, h_div⟩
    have hm_even : Even (n - 1) := by exact (Nat.not_even_iff_odd.mp (by assumption)).tsub_odd odd_one
    have hm_not_zero : n - 1 ≠ 0 := by exact(1).sub_ne_zero_of_lt (Ne.lt_of_le (by cases·▸hcomp with valid) (hn_pos) )
    have hn_gt_one : n > 1 := by omega
    have hV_eq := bernoulli_den_vsc (n - 1) hm_even hm_not_zero
    have hV_div : ∀ p : ℕ, p.Prime → p ∣ n → p ∣ (_root_.bernoulli (n - 1)).den := by
      intro p hp hpn
      have hdiv := h_div p hp hpn
      rw [hV_eq]
      have hmem := mem_filter_of_carmichael_prime n (n - 1) p rfl hn_gt_one hp hpn hdiv
      exact dvd_prod_of_mem (n - 1) p hmem
    have ha_sub := a_squarefree_of_conditions n (_root_.bernoulli (n - 1)).num (_root_.bernoulli (n - 1)).den hn_pos hsq hV_div
    have ha_eq := a_eq_n_sq_div_gcd n hn_pos
    have ha : Squarefree (a n) := by
      rwa[ha_eq]
    exact ⟨hcomp, ha⟩
  -- EVOLVE-BLOCK-END
