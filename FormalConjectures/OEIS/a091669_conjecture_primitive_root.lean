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




open Nat BigOperators

/--
A091669: $a(n) = \frac{2^{n-1}}{n!} \prod_{k=1}^{n-1} (2^k-1)$.
The sequence $a(n)$ is composed of natural numbers, thus we define it as a function $\mathbb{N} \to \mathbb{N}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0 -- Sequence is defined for n >= 1.
  else
    let n_pred : ℕ := n.pred

    -- The numerator of the expression. Both factors are in ℕ.
    let numerator : ℕ := (2 ^ n_pred) * (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1)

    -- The denominator is $n!$.
    let denominator : ℕ := n.factorial

    -- The division is exact, since the result is an integer sequence.
    numerator / denominator

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
def P_prod (n : ℕ) : ℕ := (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)

lemma a_mul_fac (n : ℕ) (hn : n > 2) :
  a (n - 1) * (n - 1).factorial = 2 ^ (n - 2) * P_prod n := by
  rw [←n.sub_add_cancel hn.le,a,gt_iff_lt, P_prod] at*
  refine Nat.div_mul_cancel (if R :_=0 then⟨0,R⟩else(Nat.factorization_le_iff_dvd (by positivity) R).mp fun and=>? _)
  use if a :_ then((((Nat.factorization_def _ a)).trans_le) ? _)else((Nat.factorization_eq_zero_of_non_prime _) a).trans_le ↑bot_le
  by_cases hS: and ∣ (2)
  · apply (by_contra ↑(absurd ((Fact.mk a)) fun and=>. ( (padicValNat_factorial ↑(Nat.le_succ _)).trans_le _) ) )
    norm_num[(Nat.prime_dvd_prime_iff_eq a _).1 (hS:)] at R⊢
    norm_num[ Finset.sum_Ico_eq_sum_range, R,Finset.sum_range_succ']
    use le_add_right ((n-2).strongRec fun and c=>match and with|0=>by norm_num | S+1=>.trans (by rw [Nat.log]) ? _)
    trans∑ a ∈.range ((2).log ((S+1+1)/2)+1),(S+2) / 2^(1+(a+1))+(S+2) / 2
    · norm_num[add_comm 1,pow_add, add_assoc]
      use if a:_ then Finset.sum_le_sum_of_subset (( Finset.range_subset.2 a))else(Finset.sum_subset (List.range_subset.2 (not_lt.1 fun and=>?_)) fun A B=>Nat.div_eq_of_lt ∘?_).ge
      · use a fun a=>List.mem_range.2 ∘and.trans'
      · use (by valid ∘(2).lt_pow_of_log_lt (by decide)) ∘not_lt.1 ∘mt @List.mem_range.2
    · exact (Nat.add_le_add_right ((c (S/2) (by valid)).trans' (by norm_num[add_comm 1,pow_succ',←Nat.div_div_eq_div_mul, Finset.sum_range_succ',add_assoc])) _).trans ( (by valid))
  convert(padicValNat_factorial (Nat.le_succ _)).trans_le _
  · exact ⟨a,⟩
  trans∑ a ∈.Ico (1) (n-2+1),.factorization (2^(a)-1) and
  · trans∑ a ∈.Ico (1) (n-2+1),∑ B ∈.Ico (1) (and.log (n-2+1)+2),ite (and^B ∣2^a-1) (1) 0
    · use(Finset.sum_le_sum fun R M=>by_contra (absurd ((Fact.mk a)) fun and' =>. ( if I:IsUnit (2 :ZMod (and^R)) then(? _)else(?_)))).trans_eq Finset.sum_comm
      · convert(I.elim fun A B=> if I:.image (orderOf A*.) (.Icc (1) ((n-2+1)/and^R)) ⊆(Finset.Ico (1) (n-2+1)).filter (and^R ∣2^.-1) then(? _)else _)
        · apply(((1).card_Icc _)▸ Finset.card_image_of_injective ↑_ ↑(mul_right_injective₀ ↑(orderOf_pos A).ne'))▸(Finset.card_mono I).trans_eq ↑( Finset.card_filter _ _)
        convert I.elim (Finset.image_subset_iff.2 fun and α=>(Finset.mem_Icc.1 α).elim fun and β=> Finset.mem_filter.2 ⟨ Finset.mem_Ico.2 ⟨mul_pos (orderOf_pos A) and, _⟩,_⟩)
        · exact (mul_lt_mul_of_pos_right ↑(orderOf_le_card_univ.trans_lt (by·norm_num[a.one_lt, R.ne_of_gt ↑( Finset.mem_Ico.mp M).left, true,Nat.totient_lt])) and).trans_le.comp (mul_right_mono β).trans (Nat.mul_div_le _ _)
        push_cast[eq_self,pow_mul,←B,pow_orderOf_eq_one, sub_self, one_pow,<-ZMod.natCast_eq_zero_iff,←Units.val_pow_eq_pow_val,Nat.one_le_pow]
        exact (Nat.cast_pred (by positivity)).trans (by zify[←B,←Units.val_pow_eq_pow_val, sub_self, one_pow,pow_orderOf_eq_one])
      · rcases I.comp (ZMod.isUnit_iff_coprime _ _).mpr ((a.coprime_iff_not_dvd.mpr (hS)).symm.pow_right R)
    · use Finset.sum_le_sum fun and(A) =>.trans (by rw [← Finset.card_filter]) (( Finset.card_mono fun and=>by simp_all[a.pow_dvd_iff_le_factorization _, Finset.prod_eq_zero_iff]).trans_eq ((1).card_Icc (.factorization _ _)))
  · simp_all[ Finset.prod_eq_zero_iff,Nat.factorization_prod]

lemma h_fac_div_lemma (n : ℕ) (hn : n > 2) (hdiv : n ∣ a (n - 1) + 2 ^ (n - 2)) :
  n.factorial ∣ 2 ^ (n - 2) * (P_prod n + (n - 1).factorial) := by
  have ha := a_mul_fac n hn
  rcases hdiv with ⟨k, hk⟩
  have h2 : (a (n - 1) + 2 ^ (n - 2)) * (n - 1).factorial = n * k * (n - 1).factorial := by rw [hk]
  have h3 : a (n - 1) * (n - 1).factorial + 2 ^ (n - 2) * (n - 1).factorial = k * n.factorial := by induction↑hn with apply(( add_mul _ _ _).symm.trans h2).trans.comp (mul_assoc _ _ _).trans <|mul_left_comm _ _ _
  have h4 : 2 ^ (n - 2) * P_prod n + 2 ^ (n - 2) * (n - 1).factorial = k * n.factorial := by simp_all only
  have h5 : 2 ^ (n - 2) * (P_prod n + (n - 1).factorial) = n.factorial * k := by rwa[mul_comm (n : ℕ)!, mul_add]
  exact ⟨k, h5⟩

lemma not_pow2 (n : ℕ) (hn : n > 2) (hdiv : n.factorial ∣ 2 ^ (n - 2) * (P_prod n + (n - 1).factorial)) :
  ¬ ∃ k, n = 2 ^ k := by
  rewrite [not_exists, P_prod,gt_iff_lt] at*
  use fun and J=>match n with|n + 1=>absurd ((Nat.factorization_le_iff_dvd (by positivity) (by positivity)).2 hdiv (2)) ?_
  norm_num [J,.!, true, (n.factorial_ne_zero), ↑(n).add_sub_add_right, true,Nat.factorization_def] at hn⊢
  convert(((congr_arg _) (padicValNat_factorial (by constructor))).ge.trans_lt' _)
  · decide
  convert(padicValNat.mul (Nat.two_pow_pos _).ne' _).trans_lt ((Nat.add_le_add (padicValNat.prime_pow _).le (padicValNat.eq_zero_of_not_dvd _).le).trans_lt _)
  · positivity
  · exact (Nat.prime_two.prime.not_dvd_finset_prod fun and μ=>by norm_num[(Finset.mem_Ico.1 μ).1.trans_lt']).comp (Nat.dvd_add_left ((2).factorial_dvd_factorial hn.le_pred)).1
  refine match and with | S+1=>(((congr_arg _) ((by rw [Nat.log_eq_of_pow_le_of_lt_pow (by valid:2 ^S ≤ _) (by valid), Finset.sum_Ico_eq_sum_range]))).ge.trans_lt') ?_
  use(add_zero _).trans_lt ((tsub_lt_iff_right hn.le).2 (S.succ_sub_one.symm▸ S.rec (by bound) ?_ n J))
  simp_rw [add_comm 1,pow_succ',←Nat.div_div_eq_div_mul, Finset.sum_range_succ']
  refine fun and A B x =>(ge_of_eq (by rw [ Finset.sum_congr rfl fun and i=>by rw [pow_succ',←Nat.div_div_eq_div_mul]])).trans_lt' (by match A (B/2) with | S=>omega)

lemma odd_prime_of_not_pow2 (n : ℕ) (hn : n > 2) (hcomp : ¬ Nat.Prime n) (hnot : ¬ ∃ k, n = 2 ^ k) :
  ∃ p, Nat.Prime p ∧ p ∣ n ∧ Odd p := by
  exact (not_forall.mp (hnot ⟨ _, n.prod_primeFactorsList (by((omega)))▸List.prod_eq_pow_card _ _ ·⟩)).imp fun and(a)=>by simp_all-contextual [↑(Nat.Prime.odd_of_ne_two)]

lemma odd_prime_factor_of_composite (n : ℕ) (hn : n > 2) (hcomp : ¬ Nat.Prime n)
  (hdiv : n.factorial ∣ 2 ^ (n - 2) * (P_prod n + (n - 1).factorial)) :
  ∃ p, Nat.Prime p ∧ p ∣ n ∧ Odd p := by
  have h_not_pow2 := not_pow2 n hn hdiv
  exact odd_prime_of_not_pow2 n hn hcomp h_not_pow2

lemma p_pow_div_P (n p : ℕ) (hp : Nat.Prime p) (hp_odd : Odd p) :
  p ^ ((n - 2) / (p - 1)) ∣ P_prod n := by
  rw[p.odd_iff,P_prod]at*
  refine if a:_=0 then ⟨0,a⟩else(((hp.pow_dvd_iff_le_factorization a)).mpr.comp (Nat.factorization_def _ hp).ge.trans') ?_
  trans∑ a ∈.Ico (1) (n-1),ite (p ∣02 ^a-1) (1) 0
  · replace a:.image ((p-1)* ·) (.Icc 1 ( (n-2) /(p-1))) ⊆(Finset.Ico (1) (n-1)).filter (p ∣02^·-1)
    · use Finset.image_subset_iff.2 fun and μ=>(Finset.mem_Icc.1 μ).elim fun and β=> Finset.mem_filter.2 ⟨ Finset.mem_Ico.2 ⟨mul_pos hp.pred_pos and,((mul_right_mono β).trans (Nat.mul_div_le _ _)).trans_lt ?_⟩,?_⟩
      · match (n : ℕ) with|0 | (01) =>rcases(p-1).zero_div▸ and.trans_le β | S+2 => constructor
      rw [←CharP.cast_eq_zero_iff (ZMod p),Nat.cast_pred (@Nat.two_pow_pos _),Nat.cast_pow, sub_eq_zero,pow_mul, match Fact.mk hp with | S =>ZMod.pow_card_sub_one_eq_one ↑( (ZMod.isUnit_iff_coprime _ _).mpr _).ne_zero, one_pow]
      simp_all[p.odd_iff]
    · apply ((1).card_Icc _)▸(Finset.card_image_of_injective @_ ↑(mul_right_injective₀ hp.pred_pos.ne'))▸(Finset.card_mono a).trans_eq (Finset.card_filter _ _)
  · simp_all[<-Nat.factorization_def,Finset.sum_le_sum,Nat.one_le_iff_ne_zero,hp.ne_one,Finset.prod_eq_zero_iff,Nat.factorization_prod]
    exact ( Finset.card_eq_sum_ones ( _)).symm▸(Finset.sum_le_sum (by simp_all[·.one_le_iff_ne_zero,Nat.one_le_iff_ne_zero,Nat.factorization_eq_zero_iff])).trans ( Finset.sum_le_sum_of_subset (by bound))

lemma padicValNat_fac_eq (m p : ℕ) (hp : Nat.Prime p) :
  padicValNat p m.factorial = m / p + padicValNat p (m / p).factorial := by
  apply (by_contra ↑(absurd (Fact.mk hp) fun and=>. ( (padicValNat_factorial (Nat.le_succ _)).trans.comp (.symm) _) ) )
  norm_num[padicValNat_factorial (Nat.succ_le_succ (p.log_monotone (m.div_le_self p))),add_comm, add_left_comm,m.div_div_eq_div_mul,pow_succ', Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ']

lemma vp_fac_bound (m p : ℕ) (hp : Nat.Prime p) (hm : m ≥ 1) :
  (p - 1) * padicValNat p m.factorial ≤ m - 1 := by
  use Nat.le_sub_one_of_lt (m.strongRec (fun a s=>? _) hm hp.two_le)
  use fun and x =>match a with|n + 1=> if I:p ∣n + 1 then(I.elim) ?_ else(? _)
  · exact (fun R M =>match Fact.mk hp with | S=>(M▸padicValNat_factorial_mul _)▸by linear_combination R*p.sub_add_cancel hp.pos+s R (M▸lt_mul_left (by cases R with valid) x) (by cases R with valid) x -M)
  · cases n.eq_zero_or_pos with norm_num[padicValNat.mul,padicValNat.eq_zero_of_not_dvd I,.!,Fact.mk,n.factorial_ne_zero, (s _ _ _ _).trans,Nat.succ_le, *]

lemma val_fac_lt_m (n p : ℕ) (hn : n > 2) (hp : Nat.Prime p) (hp_div : p ∣ n) (hp_odd : Odd p) (hcomp : ¬ Nat.Prime n) :
  padicValNat p (n - 1).factorial < (n - 2) / (p - 1) := by
  rcases hp_div with ⟨k, hk⟩
  have hk_comm : n = k * p := by rwa [p.mul_comm] at hk
  have h_p_ge_3 : p ≥ 3 := by apply hp.two_le.lt_of_ne (by cases· with (contradiction))
  have hk2 : k ≥ 2 := by exact (k : ℕ).two_le_iff.mpr (by repeat use fun and=>by simp_all[])
  have h_div_p : (n - 1) / p = k - 1 := by match k with | S+1 =>exact (hk▸Nat.div_eq_of_lt_le (p.mul_comm S▸Nat.le_pred_of_lt ((Nat.mul_lt_mul_left hp.pos).symm.mp (by constructor))) ((Nat.sub_lt (by (bound ) ) one_pos).trans_eq (by ring!)) )
  have h_step : padicValNat p (n - 1).factorial = k - 1 + padicValNat p (k - 1).factorial := by refine hk▸match k with | S+1=>by_contra (absurd (Fact.mk hp) fun and=>. (.trans (by rw [p.mul_succ,p.add_sub_assoc hp.pos,←Nat.factorial_mul_ascFactorial,Nat.ascFactorial_eq_prod_range]) ?_))
                                                                                                simp_all[padicValNat.mul, add_assoc, S.add_sub_cancel _,padicValNat_factorial_mul,add_comm 1,hp.prime.dvd_finset_prod_iff,Nat.not_dvd_of_pos_of_lt _,lt_tsub_iff_right, true,Nat.factorial_ne_zero _, Finset.prod_eq_zero_iff]
                                                                                                rw [←add_comm,padicValNat.eq_zero_of_not_dvd.comp ( hp).prime.not_dvd_finset_prod fun and=>mt (p.dvd_add_right ⟨ S, rfl⟩).mp ∘mt p.eq_zero_of_dvd_of_lt ∘by valid ∘ Finset.mem_range.1, add_zero]
  have h_bound : (p - 1) * padicValNat p (k - 1).factorial ≤ k - 2 := by refine k.sub_add_cancel (le_of_lt ↑(hk2))▸(k-1).strongRec (@ fun and x =>?_) (Nat.sub_pos_of_lt ↑hk2)
                                                                         use fun and' =>match and with | (n + 1) => if a:p ∣n + 1 then (a.elim) ?_ else(? _)
                                                                         · exact (fun A B=>match Fact.mk hp with | S=>.trans (by rw [B,padicValNat_factorial_mul,mul_add]) (by match A with | S+1 =>nlinarith! only[p.sub_add_cancel hp.pos, B, true,(x _) (B▸lt_mul_left S.succ_pos (by valid) ) S.succ_pos]))
                                                                         · cases n.eq_zero_or_pos with norm_num[padicValNat.mul,padicValNat.eq_zero_of_not_dvd a,.!,Fact.mk,n.factorial_ne_zero,(x _ _ _).trans n.pred_le,Nat.succ_sub_succ_eq_sub _, *]
  have h_mul : (p - 1) * padicValNat p (n - 1).factorial = (p - 1) * (k - 1) + (p - 1) * padicValNat p (k - 1).factorial := by rw [←mul_add _,h_step]
  have h_le : (p - 1) * padicValNat p (n - 1).factorial ≤ (p - 1) * (k - 1) + k - 2 := by push_cast [hk2, h_bound,Nat.add_le_add_left,Nat.add_sub_assoc,h_mul]
  have h_alg : (p - 1) * (k - 1) + k - 2 = n - p - 1 := by exact (hk▸match k,p with | S+1, L+1=>L.succ_sub_one.symm▸S.succ_sub_one.symm▸L.succ_mul_succ S▸by valid)
  have h_mul_add : (padicValNat p (n - 1).factorial + 1) * (p - 1) ≤ n - 2 := by exact (.trans (by rw [Nat.succ_mul,mul_comm]) ((by valid ∘(2).mul_le_mul_left p) (hk2)))
  exact (Nat.le_div_iff_mul_le hp.pred_pos).2 (by assumption)

lemma p_pow_not_div_fac (n p : ℕ) (hn : n > 2) (hp : Nat.Prime p) (hp_div : p ∣ n) (hp_odd : Odd p) (hcomp : ¬ Nat.Prime n) :
  ¬ (p ^ ((n - 2) / (p - 1)) ∣ (n - 1).factorial) := by
  have h1 := val_fac_lt_m n p hn hp hp_div hp_odd hcomp
  rwa [match Fact.mk hp with | S =>padicValNat_dvd_iff_le (by(positivity)),not_le]

lemma padic_contradiction (A B n p k m : ℕ) (hp_odd : Odd p) (hp_prime : Nat.Prime p)
  (hk : p ^ k ∣ B) (hk_exact : ¬ (p ^ (k + 1) ∣ B)) (hm : p ^ m ∣ A) (hm_gt : m > k)
  (h_div : p ^ (k + 1) ∣ 2 ^ n * (A + B)) : False := by
  simp_all only [Nat.dvd_add_right.comp (pow_dvd_pow p (by assumption ) ).trans (hm), (hp_odd.coprime_two_right.pow _ _).dvd_mul_left]

lemma prime_of_div (n : ℕ) (hn : n > 2) (hdiv : n ∣ a (n - 1) + 2 ^ (n - 2)) : Nat.Prime n := by
  have h1 := h_fac_div_lemma n hn hdiv
  by_contra hcomp
  have h_p_exists := odd_prime_factor_of_composite n hn hcomp h1
  rcases h_p_exists with ⟨p, hp, hp_div, hp_odd⟩
  have hA := p_pow_div_P n p hp hp_odd
  have hB_not := p_pow_not_div_fac n p hn hp hp_div hp_odd hcomp
  let k := padicValNat p (n - 1).factorial
  have hk : p ^ k ∣ (n - 1).factorial := by apply @pow_padicValNat_dvd
  have hk_exact : ¬ (p ^ (k + 1) ∣ (n - 1).factorial) := by simp_all[padicValNat_dvd_iff_le,k,Fact.mk,Nat.factorial_ne_zero]
  let m := (n - 2) / (p - 1)
  have hm_gt : m > k := by
    exact val_fac_lt_m n p hn hp hp_div hp_odd hcomp
  have h_p_div_n_fac : p ^ (k + 1) ∣ n.factorial := by exact (pow_succ' p _)▸by cases@@hn with apply mul_dvd_mul hp_div ↑hk
  have h_div_p : p ^ (k + 1) ∣ 2 ^ (n - 2) * (P_prod n + (n - 1).factorial) := by valid
  exact padic_contradiction (P_prod n) (n - 1).factorial (n - 2) p k m hp_odd hp hk hk_exact hA hm_gt h_div_p

lemma prim_root_of_prime (n : ℕ) (hn : n > 2) (hprime : Nat.Prime n) (hdiv : n ∣ a (n - 1) + 2 ^ (n - 2)) :
  IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  push_cast[a, add_eq_zero_iff_eq_neg,Nat.totient_prime hprime,<-ZMod.natCast_eq_zero_iff,.> ·]at*
  convert (by_contradiction fun and=> absurd (Fact.mk hprime) fun and' =>(@IsCyclic.exists_generator (ZMod n)ˣ _ _).elim fun and x => if a: (∏ a ∈.Ico (1) (n-1), (2^a-1):ZMod n)/(n-1)! = -1 then(? _)else @ _)
  · replace hdiv:orderOf and=n-1:=by rw [orderOf_eq_card_of_forall_mem_zpowers x,Nat.card_eq_fintype_card,ZMod.card_units]
    convert‹¬_› (IsPrimitiveRoot.mk_of_lt _ hprime.pred_pos (ZMod.pow_card_sub_one_eq_one (by match n with | S+3=>nofun)) fun and A B R=> _)
    simp_all[ Finset.prod_eq_zero_iff.mpr ⟨ and, _⟩,Nat.succ_le]
  rw[dif_neg (by valid), Nat.cast_div] at hdiv
  · simp_all -contextual[←eq_inv_mul_iff_mul_eq₀ _, (by match n with | S+3=>nofun: (2 :ZMod n)≠0),n.sub_sub, mul_div_assoc _ _]
  · refine if a:_=0 then⟨0,congr_arg _ a⟩else((Nat.factorization_le_iff_dvd (by positivity) (Nat.mul_ne_zero (by positivity) a)).1 fun and=>? _)
    use if I:_ then(((Nat.factorization_def _ I).trans_le) ? _)else((Nat.factorization_eq_zero_of_non_prime _) I).trans_le bot_le
    by_cases h:and ∣2
    · apply (by_contra ↑(absurd (Fact.mk I) fun and=>. ( (padicValNat_factorial (Nat.le_succ _)).trans_le _) ) )
      norm_num[a,(Nat.prime_dvd_prime_iff_eq I _).mp h, Finset.sum_Ico_eq_sum_range _, Finset.sum_range_succ']
      use le_add_right (Nat.le_sub_one_of_lt ((n-1).strongRec (fun A B=>?_) (Nat.le_sub_one_of_lt hn)))
      rewrite [Nat.log]
      intros
      convert_to∑n ∈.range ((2).log (A/2)+1), A/2^(1+ (n + 1))+A/2<A
      · show∑ a ∈.range (.log _ _),_ +_ = _
        exact (congr_arg₂ _) ((congr_arg₂ _) ((congr_arg _) ((2).log_eq_of_pow_le_of_lt_pow (Nat.mul_le_of_le_div _ _ _ ((2).pow_log_le_self (by valid))) (A.lt_mul_of_div_lt ((2).lt_pow_succ_log_self (by decide) _) (by decide)))) rfl ) rfl
      · simp_rw [add_comm (@1), Finset.sum_range_succ',pow_succ',← A.div_div_eq_div_mul] at B⊢
        match A with|2|3=>norm_num | S+4=>exact (Nat.add_lt_add_right (B _ (Nat.div_lt_self S.succ.succ.succ.succ_pos (by decide)) (by push_cast[Nat.le_div_iff_mul_le])) _).trans_le (by omega)
    convert (padicValNat_factorial (Nat.le_succ _)).trans_le (@ _)
    · exact ⟨ I⟩
    trans∑ a ∈.Ico (1) (n-1),.factorization (2^a-1) and
    · trans∑ a ∈.Ico (1) (n-1),∑x ∈.Ico (1) (and.log (n-1)+2),ite (and^x ∣2^a-1) (1) 0
      · use(Finset.sum_le_sum fun R M=>by_contra (absurd (Fact.mk I) fun and' =>. ( (( (ZMod.isUnit_iff_coprime _ _).2<|(I.coprime_iff_not_dvd.2 h).symm.pow_right R).elim) ?_))).trans_eq Finset.sum_comm
        refine fun a s=> if I:.image ↑(orderOf a* ·) (.Icc (1) (((n)-1)/ and^ R)) ⊆(Finset.Ico (1) (n-1)).filter (and ^R ∣2 ^ ·-1) then(? _)else(? _)
        · apply ((1).card_Icc _)▸(Finset.card_image_of_injective _ (mul_right_injective₀ (orderOf_pos a).ne'))▸(Finset.card_mono I).trans_eq (Finset.card_filter _ _)
        push_cast[pow_mul,orderOf_pos,←CharP.cast_eq_zero_iff (ZMod (and^R)), Finset.image_subset_iff, Finset.mem_Icc, Finset.mem_Ico, Finset.mem_filter,Nat.succ_le,Nat.two_pow_pos] at M(s)I
        convert I.elim fun and⟨A, B⟩=>s▸mod_cast⟨⟨mul_pos ((orderOf_pos a)) A,((Nat.mul_lt_mul_right ↑A).mpr ↑(orderOf_le_card_univ.trans_lt _)).trans_le.comp (mul_right_mono (B) ).trans (Nat.mul_div_le _ _)⟩,_⟩
        · norm_num[Nat.totient_lt, M.1.ne', (and').out.one_lt]
        · norm_num[pow_orderOf_eq_one]
      · use Finset.sum_le_sum fun and(A) =>.trans (by rw [← Finset.card_filter]) (( Finset.card_mono fun and=>by norm_num+contextual[I.pow_dvd_iff_le_factorization (Finset.prod_ne_zero_iff.1 a _ A)]).trans_eq ((1).card_Icc (.factorization _ _)))
    · simp_all[Nat.factorization_prod,Finset.prod_eq_zero_iff]
  · use (by valid ∘hprime.dvd_factorial.1.comp (CharP.cast_eq_zero_iff _ _ _).1)
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (n : ℕ) (hn : n > 2) : n ∣ (a (n - 1) + 2 ^ (n - 2)) → Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  -- EVOLVE-BLOCK-START
  intro hdiv
  have hprime := prime_of_div n hn hdiv
  have hprim := prim_root_of_prime n hn hprime hdiv
  exact ⟨hprime, hprim⟩
  -- EVOLVE-BLOCK-END
