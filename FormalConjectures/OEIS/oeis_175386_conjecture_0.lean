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




open scoped BigOperators

/--
A175386: $a(n)$ is the denominator of the sum
$$\sum_{i=1}^n \frac{1}{i} \binom{2n-i-1}{i-1}$$
-/
def a (n : ℕ) : ℕ :=
  (Finset.sum (Finset.Icc 1 n) fun i : ℕ =>
    -- The upper index is $2n - i - 1$, which is equivalent to $2n - (i+1)$ in $\mathbb{N}$ for $i \le n$.
    -- The lower index $i-1$ is standard subtraction in $\mathbb{N}$.
    let num : ℕ := Nat.choose (2 * n - (i + 1)) (i - 1)
    (num : ℚ) / (i : ℚ)
  ).den

/-- The sum which A175386 $a(n)$ is the denominator of. -/
def S (n : ℕ) : ℚ :=
  Finset.sum (Finset.Icc 1 n) fun i : ℕ =>
    let num : ℕ := Nat.choose (2 * n - (i + 1)) (i - 1)
    (num : ℚ) / (i : ℚ)

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
def lucas : ℕ → ℤ
| 0 => 2
| 1 => 1
| n + 2 => lucas (n + 1) + lucas n

lemma a_not_one_of_S_not_int {n : ℕ} (h : ¬ ∃ (k : ℤ), S n = (k : ℚ)) : a n ≠ 1 := by
  norm_num[a, S] at h⊢
  exact ( h _) ∘.symm ∘ Rat.coe_int_num_of_den_eq_one

lemma S_eq_lucas (n : ℕ) (hn : 0 < n) : (2 * n : ℚ) * S n = (lucas (2 * n) : ℚ) - 1 := by
  rw [←eq_comm, S, sub_eq_add_neg]
  trans (2 * (n : ℕ)) *∑ a ∈.Icc (1) (2 *n), ( (2 *(n) - (a+1)).choose (a-1)/a: (ℚ ) )
  · replace hn : ∀ (n : ℕ), 1 ≤n →(lucas n:ℚ)+-1=n*∑ a ∈.Ico (1) (n : ℕ),((n-(a+1)).choose (a-1)/a:ℚ) :=Nat.strongRec fun and J=>match and with|0|1=>?_ | S+2=>?_
    · push_cast[add_comm 1,lucas, mul_add, add_assoc,Nat.forall_lt_succ, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ']at*
      refine fun and=>match S with|0=>by {norm_num [lucas] } | S+1=>.trans (by rw [J.left.right S.succ_pos,eq_sub_of_add_eq (J.right and), Finset.mul_sum, Finset.mul_sum _, Finset.sum_range_succ']) ((symm) ? _)
      norm_num[add_comm (1:ℚ),add_assoc, mul_add, add_div, S.add_sub_add_right, Finset.mul_sum, Finset.sum_range_succ,Nat.choose]
      field_simp[add_comm (S:ℚ), ( fun and=>by valid ∘ Finset.mem_range.1 : ∀ a ∈ Finset.range S,S-a = S-(a+1)+1), add_assoc]
      push_cast+contextual[add_comm (S:ℚ), ( fun and=>by valid ∘ Finset.mem_range.1 : ∀ a ∈ Finset.range S,S-a = S-(a+1)+1), add_assoc, Finset.sum_add_distrib,Nat.choose]
      refine((congr_arg₂ _) (( Finset.sum_congr rfl fun and i=>?_).trans Finset.sum_add_distrib) rfl ).trans (.trans (add_assoc _ _ _) (congr_arg _ (add_left_comm _ _ _)))
      refine eq_add_of_sub_eq' ((sub_div _ _ _).symm.trans.comp (div_eq_div_iff (by norm_cast) (by((norm_cast)))).2 (sub_mul _ _ _|>.trans ( sub_eq_of_eq_add ↑(mod_cast(?_)))))
      nlinarith[(S- (and + 1)).succ_mul_choose_eq and, S.sub_add_cancel (List.mem_range.1 i),(S- (and+1)).choose_succ_succ and]
    · exact (hn _) (by valid) |>.trans (congr_arg₂ _ (by zify) (.symm (( Finset.sum_Ico_succ_top (by valid) _).trans (.trans (by rw [Nat.sub_eq_zero_of_le le_self_add,Nat.choose_eq_zero_of_lt (by valid)]) (by ring)))))
    · trivial
    · exact fun and=>.trans (add_neg_cancel _) ((mul_zero _)).symm
  · exact (congr_arg _) (Finset.sum_subset (Finset.Icc_subset_Icc_right (by valid)) fun and R M=>.trans (by rw [Nat.choose_eq_zero_of_lt (not_le.1 (M ∘ Finset.mem_Icc.2 ∘(Finset.mem_Icc.1 R).elim (by valid)))]) (by ring)).symm

lemma lucas_mod_four (n : ℕ) : lucas n % 4 =
  if n % 6 = 0 then 2
  else if n % 6 = 1 then 1
  else if n % 6 = 2 then 3
  else if n % 6 = 3 then 0
  else if n % 6 = 4 then 3
  else 3 := by
  refine n.strongRec fun and(a)=>match and with|0|1|2|3|4 | (5) =>rfl | S+6=>.trans (by rw [lucas,lucas, lucas,lucas,lucas]) ?_
  exact S.add_mod_right 6▸a S (by valid)▸by valid

lemma lucas_not_eq_even (n : ℕ) (hn : 1 < n) (he : n % 2 = 0) (k : ℤ) : (2 * (n : ℤ)) * k ≠ lucas (2 * n) - 1 := by
  delta Ne lucas
  convert_to (2 *↑n*k≠2* (2 *n+1).fib- (2 *n).fib-1)
  · exact (Eq.congr_right ∘congr_arg (@ ·-1 ) ) (by induction (2 * _) using@Nat.twoStepInduction with|zero|one=> constructor| more P A B=>exact P.fib_add_two▸Nat.fib_add_two.symm▸by grind)
  rewrite[ Ne, sub_sub _, n.fib_two_mul,(n).fib_two_mul_add_one, mul_assoc]
  obtain ⟨x, _⟩| ⟨a, _⟩:= n.fib.even_or_odd
  · exact (by valid▸add_mul x _ _▸by valid)
  simp_all[mul_left_comm, add_mul,mul_sub,sq,le_mul_of_one_le_of_le,n.fib_le_fib_succ]
  push_cast[mul_assoc, mul_add, mul_sub, add_assoc,mul_left_comm (n : ℤ),le_mul_of_one_le_of_le,‹_›▸n.fib_le_fib_succ]
  exact (mt (·.trans (by rw [mul_left_comm (a : ℤ)])) ( ((by valid: (2 : Int) ∣n).mul_right k).elim ((Even.two_dvd (by norm_num[parity_simps] :Even ( (n + 1).fib* (n + 1).fib+ (n + 1).fib : ℤ))).elim (by grind))))

lemma lucas_odd_sq (n : ℕ) (ho : n % 2 = 1) : lucas (2 * n) = (lucas n)^2 + 2 := by
  replace : ∀ (n : ℕ),lucas n=2* (n + 1).fib-n.fib:=Nat.twoStepInduction rfl (↑rfl) ?_
  · zify[n.fib_two_mul,n.fib_two_mul_add_one, this, sub_sq, mul_pow]
    exact (ho▸n.div_add_mod _)▸.trans (by rw [Nat.cast_sub.comp (Nat.fib_le_fib_succ).trans (by valid), Nat.cast_mul]) (by exact(n/2).rec ↑rfl fun and(a) => (2 *and+2).fib_add_two▸ (2 *and+1).fib_add_two▸by(grind ) )
  · simp_all![Nat.fib_add_two.trans (add_comm _ _), mul_add, sub_add_sub_comm]

def fib : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => fib (n + 1) + fib n

lemma fib_dvd (a b : ℕ) : fib a ∣ fib (a * b) := by
  convert a.fib_dvd _ ⟨b, rfl⟩
  zify[(Nat.twoStepInduction rfl rfl (by simp_all![fib,add_comm,·.fib_add]) : ∀x,fib x =x.fib)]

lemma fib_gcd (a b : ℕ) : (fib a).gcd (fib b) = fib (a.gcd b) := by
  replace : ∀ (x : ℕ),fib x =x.fib:=Nat.twoStepInduction rfl (↑rfl) (by simp_all![Nat.fib_add _,add_comm])
  exact (funext this▸congr_arg ↑_ (@a.fib_gcd _).symm)

lemma dvd_fib_gcd (p A B : ℕ) (hA : (p : ℤ) ∣ fib A) (hB : (p : ℤ) ∣ fib B) : (p : ℤ) ∣ fib (A.gcd B) := by
  simp_all only[(Nat.twoStepInduction rfl rfl fun and a s=>by simp_all! only[add_comm, and.fib_add_two,Nat.cast_add]:∀x,fib x =x.fib),Int.ofNat_dvd, A.fib_gcd,p.dvd_gcd]

lemma fib_sq_prime_mod_p (p : ℕ) (hp : Nat.Prime p) (ho : p % 2 = 1) (hp5 : p ≠ 5) : (p : ℤ) ∣ (fib p)^2 - 1 := by
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by_contra fun and=>absurd ((Fact.mk hp) ) fun and' =>absurd (Real.coe_fib_eq p) ? _)
  push_cast[Ne, sub_eq_zero,div_pow]at*
  rw [←sub_div, add_pow, sub_pow,eq_div_iff (by norm_num)]
  obtain ⟨s, rfl⟩:=p.odd_iff.mpr ho
  norm_num[pow_mul,pow_add, true, Finset.sum_range_succ] at ho⊢
  replace ho : Finset.range (2 *s)=.image (2 *.) (.range s)∪.image (2 *·+1) (.range s)
  · exact s.rec rfl (by simp_all [ Finset.range, mul_add])
  rw[ho, Finset.sum_union, Finset.sum_union]
  · norm_num[pow_mul,Nat.add_sub_add_right _,pow_add]
    by_cases h: (2 *s+1).fib*4^s =∑ a ∈.range s,5 ^ (s-a) * (2 *s+1).choose (2 *a)+ (2 *s+1)
    · apply_fun(· : ℕ →ZMod (2 *s + 1)) at h
      rw[Nat.cast_mul,Nat.cast_add,Nat.cast_sum,Nat.cast_pow,ZMod.natCast_self, add_zero _, Finset.sum_eq_single_of_mem 0 ↑(List.mem_range.mpr ((2).lt_of_mul_lt_mul_left hp.pred_pos))] at h
      · norm_num[ ←pow_mul', show (4 ^s : ZMod (2 *s + 1))=1 from ZMod.pow_card_sub_one_eq_one ((ZMod.isUnit_iff_coprime (2) (2 *s + 1)).mpr @_).ne_zero▸by·norm_num[pow_mul]]at h
        simp_all[←pow_mul',(Nat.twoStepInduction rfl rfl (by norm_num+contextual[fib,add_comm,·.fib_add]) : ∀x,fib x =x.fib),Nat.add_sub_cancel _ _▸ZMod.pow_card_sub_one_eq_one]
        rcases and ↑(ZMod.pow_card_sub_one_eq_one fun and=>by match s with | S+3=>cases and)
      · use fun and R M=>CharP.cast_eq_zero_iff _ _ _|>.2 ((hp.dvd_choose_self (by. (positivity) ) (by·linear_combination (2 *List.mem_range.1 R))).mul_left _)
    · push_cast+contextual[←@Nat.cast_inj ℝ,pow_add,pow_mul,←Nat.mul_sub,le_of_lt ∘ Finset.mem_range.1,Nat.succ_sub,Real.sq_sqrt (by·norm_num: (5: ℝ)≥0)] at h⊢
      use h ∘mul_left_cancel₀ (by norm_num:√5≠0) ∘?_ ∘(eq_div_iff (by positivity)).1
      simp_rw [mul_add,Finset.mul_sum]
      use (by linear_combination·.trans (by rw [ Finset.sum_congr rfl fun and μ=>by rw [ (by_contra ((List.mem_range.1 μ).asymm ∘by valid):_-_=2*(s-and)+ 1),pow_succ',pow_mul,Real.sq_sqrt (by bound),mul_assoc]]) / 2+1)
  · use Finset.disjoint_left.2 (Finset.forall_mem_image.2 fun and g=>mt Finset.mem_image.1 (by valid))
  · use Finset.disjoint_left.2 (Finset.forall_mem_image.2 fun and g=>mt Finset.mem_image.1 (by valid))

lemma fib_cassini (p : ℕ) (hp : 1 < p) (ho : p % 2 = 1) : fib (p + 1) * fib (p - 1) = (fib p)^2 - 1 := by
  delta fib
  exact (p.div_add_mod (2)▸ho.symm▸Nat.add_sub_cancel _ _▸(p/2).rec rfl fun and x=>(2).mul_succ and▸by linear_combination x)

lemma fib_p_minus_or_plus_one (p : ℕ) (hp : Nat.Prime p) (ho : p % 2 = 1) (hp5 : p ≠ 5) : (p : ℤ) ∣ fib (p - 1) ∨ (p : ℤ) ∣ fib (p + 1) := by
  have h1 : (p : ℤ) ∣ (fib p)^2 - 1 := fib_sq_prime_mod_p p hp ho hp5
  have h2 : fib (p + 1) * fib (p - 1) = (fib p)^2 - 1 := fib_cassini p (Nat.Prime.one_lt hp) ho
  rw [← h2] at h1
  have h_prime_dvd : (p : ℤ) ∣ fib (p - 1) * fib (p + 1) := by
    have h_comm : fib (p + 1) * fib (p - 1) = fib (p - 1) * fib (p + 1) := mul_comm _ _
    rwa [← h_comm]
  have hp_prime : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr hp
  exact Prime.dvd_or_dvd hp_prime h_prime_dvd

lemma fib_mod_p_sq_sub_one (p : ℕ) (hp : Nat.Prime p) (ho : p % 2 = 1) (hp5 : p ≠ 5) : (p : ℤ) ∣ fib (p^2 - 1) := by
  have h_cases := fib_p_minus_or_plus_one p hp ho hp5
  have h_eq : p^2 - 1 = (p - 1) * (p + 1) := by
    rw [←@@mul_comm,p.sq_sub_sq @1]
  rw [h_eq]
  rcases h_cases with h_minus | h_plus
  · have h_dvd := fib_dvd (p - 1) (p + 1)
    exact dvd_trans h_minus h_dvd
  · have h_eq2 : (p - 1) * (p + 1) = (p + 1) * (p - 1) := mul_comm _ _
    rw [h_eq2]
    have h_dvd := fib_dvd (p + 1) (p - 1)
    exact dvd_trans h_plus h_dvd

lemma odd_sq_add_one_not_dvd_five (n : ℕ) (ho : n % 2 = 1) : ¬ (5 ∣ (lucas n)^2 + 1) := by
  delta lucas
  use n.div_add_mod (2)▸ho.symm▸Int.dvd_iff_emod_eq_zero.not.mpr ((n/2).strongRec fun and x =>match and with|0|1|2|3=>by decide | S+4=>x S (by repeat constructor) ∘? _)
  exact (2).mul_add _ _▸.trans (Int.ModEq.add_right (1) (.pow (2) (by induction (2 *S) using Nat.twoStepInduction with|zero|one=>rfl| more n a s=>exact (.add s a))))

lemma minFac_neq_five (n : ℕ) (hn : 1 < n) (ho : n % 2 = 1) (h : (n : ℤ) ∣ (lucas n)^2 + 1) : Nat.minFac n ≠ 5 := by
  intro h5
  have h_div : (5 : ℤ) ∣ (lucas n)^2 + 1 := by
    have h_min := Nat.minFac_dvd n
    rw [h5] at h_min
    exact dvd_trans (by exact_mod_cast h_min) h
  have h_not := odd_sq_add_one_not_dvd_five n ho
  exact h_not h_div

lemma fib_three_n_lucas (n : ℕ) (ho : n % 2 = 1) : fib (3 * n) = fib n * ((lucas n)^2 + 1) := by
  simp_rw [Nat.succ_mul,sq]
  have : ∀x,fib x =x.fib∧lucas x =2*(x+1).fib-x.fib:=Nat.twoStepInduction (by decide) (by decide) ?_
  · push_cast[zero_mul,←@Int.cast_inj ℝ,Real.coe_fib_eq, this, zero_add]
    field_simp
    linear_combination(norm := (ring_nf ) )
    norm_num[*, sub_add_sub_comm _,←mul_pow,←sq_sub_sq,←sub_eq_add_neg,pow_mul',mul_comm (1/2-_ : ℝ),mul_assoc,sq]
    norm_num[mul_left_comm ↑√5,←sq, mul_pow]
    norm_num[←mul_assoc, Odd.neg_pow _, (n.odd_iff),ho]
  · simp_all![Nat.fib_add_two.trans ↑(add_comm _ _), mul_add, sub_add_sub_comm]

lemma minFac_dvd_fib_3n (n : ℕ) (ho : n % 2 = 1) (h : (n : ℤ) ∣ (lucas n)^2 + 1) : (Nat.minFac n : ℤ) ∣ fib (3 * n) := by
  have hl := fib_three_n_lucas n ho
  have h2 : (Nat.minFac n : ℤ) ∣ (lucas n)^2 + 1 := by
    have h_min := Nat.minFac_dvd n
    exact dvd_trans (by exact_mod_cast h_min) h
  rw [hl]
  exact dvd_mul_of_dvd_right h2 (fib n)

lemma gcd_3n_sq_sub_one (n : ℕ) (hn : 1 < n) (ho : n % 2 = 1) : (3 * n).gcd (n.minFac^2 - 1) ∣ 3 := by
  apply (Nat.coprime_iff_gcd_eq_one.2 (Nat.coprime_of_dvd fun and R M=>?_)).dvd_mul_right.1 (Nat.gcd_dvd_left _ _)
  simp_rw [and.dvd_gcd_iff,Nat.sq_sub_sq @_ @1] at M
  use fun and' => R.not_dvd_mul (fun ⟨a, _⟩=>?_) (Nat.not_dvd_of_pos_of_lt (n.minFac_prime hn.ne').pred_pos ((Nat.pred_lt n.minFac_pos.ne').trans_le (n.minFac_le_of_dvd R.one_lt and'))) M.2
  match a with|1=>use absurd ((2).dvd_trans · and') (absurd ((2).dvd_trans · n.minFac_dvd) ∘by valid) | a+2=>linarith[n.minFac_le_of_dvd R.one_lt and',zero_le (and*a), R.one_lt]

lemma minFac_dvd_fib_3 (n : ℕ) (hn : 1 < n) (ho : n % 2 = 1) (h : (n : ℤ) ∣ (lucas n)^2 + 1) : (Nat.minFac n : ℤ) ∣ fib 3 := by
  have h1 : (Nat.minFac n : ℤ) ∣ fib (3 * n) := minFac_dvd_fib_3n n ho h
  have hn_ne_one : n ≠ 1 := by omega
  have hp : Nat.Prime (Nat.minFac n) := Nat.minFac_prime hn_ne_one
  have ho_p : Nat.minFac n % 2 = 1 := by
    have h_even : ¬ 2 ∣ n := by omega
    have h_min_dvd := Nat.minFac_dvd n
    have he2 : ¬ 2 ∣ Nat.minFac n := by
      intro hc
      exact h_even (Nat.dvd_trans hc h_min_dvd)
    omega
  have hp5 : Nat.minFac n ≠ 5 := minFac_neq_five n hn ho h
  have h2 : (Nat.minFac n : ℤ) ∣ fib ((Nat.minFac n)^2 - 1) := fib_mod_p_sq_sub_one (Nat.minFac n) hp ho_p hp5
  have h3 : (Nat.minFac n : ℤ) ∣ fib ((3 * n).gcd ((Nat.minFac n)^2 - 1)) := dvd_fib_gcd (Nat.minFac n) (3 * n) ((Nat.minFac n)^2 - 1) h1 h2
  have h4 : (3 * n).gcd ((Nat.minFac n)^2 - 1) ∣ 3 := gcd_3n_sq_sub_one n hn ho
  have h_cases : (3 * n).gcd ((Nat.minFac n)^2 - 1) = 1 ∨ (3 * n).gcd ((Nat.minFac n)^2 - 1) = 3 := by
    revert h4
    generalize (3 * n).gcd ((Nat.minFac n)^2 - 1) = d
    intro hd
    have h_le := Nat.le_of_dvd (by decide) hd
    have h_pos : 0 < d := Nat.pos_of_dvd_of_pos hd (by decide)
    have hd_not_2 : d ≠ 2 := by
      intro hc
      rw [hc] at hd
      revert hd
      decide
    omega
  rcases h_cases with h_one | h_three
  · rw [h_one] at h3
    have h_fib_1 : fib 1 = 1 := rfl
    rw [h_fib_1] at h3
    have h_fib_3 : fib 3 = 2 := rfl
    rw [h_fib_3]
    exact dvd_trans h3 (by decide)
  · rw [h_three] at h3
    exact h3

lemma minFac_eq_two_of_dvd_fib_3 (n : ℕ) (hn : 1 < n) (h : (Nat.minFac n : ℤ) ∣ fib 3) : Nat.minFac n = 2 := by
  rwa [Int.natCast_dvd,Nat.prime_dvd_prime_iff_eq (n.minFac_prime hn.ne') (by decide)] at h

lemma odd_not_dvd_sq_add_one (n : ℕ) (hn : 1 < n) (ho : n % 2 = 1) : ¬ ((n : ℤ) ∣ (lucas n)^2 + 1) := by
  intro h
  have h1 := minFac_dvd_fib_3 n hn ho h
  have h2 := minFac_eq_two_of_dvd_fib_3 n hn h1
  have h3 : 2 ∣ n := by
    have h_min := Nat.minFac_dvd n
    rw [h2] at h_min
    exact h_min
  have h4 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd h3
  omega

lemma lucas_not_eq_odd (n : ℕ) (hn : 1 < n) (ho : n % 2 = 1) (k : ℤ) : (2 * (n : ℤ)) * k ≠ lucas (2 * n) - 1 := by
  intro h
  have h_sq := lucas_odd_sq n ho
  have h_eq : (2 * (n : ℤ)) * k = (lucas n)^2 + 1 := by
    calc (2 * (n : ℤ)) * k = lucas (2 * n) - 1 := h
      _ = (lucas n)^2 + 2 - 1 := by rw [h_sq]
      _ = (lucas n)^2 + 1 := by ring
  have h_dvd : (n : ℤ) ∣ (lucas n)^2 + 1 := by
    use 2 * k
    calc (lucas n)^2 + 1 = 2 * ↑n * k := h_eq.symm
      _ = ↑n * (2 * k) := by ring
  have h_not_dvd := odd_not_dvd_sq_add_one n hn ho
  exact h_not_dvd h_dvd

lemma lucas_not_eq (n : ℕ) (hn : 1 < n) (k : ℤ) : (2 * (n : ℤ)) * k ≠ lucas (2 * n) - 1 := by
  have h_cases : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h_cases with he | ho
  · exact lucas_not_eq_even n hn he k
  · exact lucas_not_eq_odd n hn ho k

-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (n : ℕ) (hn : 1 < n) : a n ≠ 1 := by
  -- EVOLVE-BLOCK-START
  apply a_not_one_of_S_not_int
  intro ⟨k, hk⟩
  have h_eq := S_eq_lucas n (by omega)
  rw [hk] at h_eq
  have h_eq2 : (2 * (n : ℤ)) * k = lucas (2 * n) - 1 := by
    exact_mod_cast h_eq
  have h_not := lucas_not_eq n hn k
  exact h_not h_eq2
  -- EVOLVE-BLOCK-END
