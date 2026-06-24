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




open BigOperators Nat Int Real Asymptotics Filter

/--
The inner sum of the formula used in A258667:
$$\sum_{\max(k-n+5, 0) \le j \le \min(k,4)} \binom{8-j}{j}\binom{2n-k+j-10}{k-j}$$
-/
private def A258667_inner_sum (n k : ℕ) : ℤ :=
  let L : ℕ := max 0 (k + 5 - n)
  let U : ℕ := min k 4
  Finset.sum (Finset.Icc L U) fun j =>
    let term1 := Nat.choose (8 - j) j
    -- The top argument of the second binomial coefficient is written in Nat subtraction form.
    let term2 := Nat.choose (2 * n + j - (k + 10)) (k - j)
    ofNat term1 * ofNat term2

/--
A258667: A total of $n$ married couples, including a mathematician M and his wife, are to be seated at the $2n$ chairs around a circular table, with no man seated next to his wife. After the ladies are seated at every other chair, M is the first man allowed to choose one of the remaining chairs. The sequence gives the number of ways of seating the other men, with no man seated next to his wife, if M chooses the chair that is 9 seats clockwise from his wife's chair.

$$a(n) = \begin{cases} 0 & \text{if } n \le 5 \\ \sum_{k=0}^{n-1}(-1)^k(n-k-1)! \sum_{\max(k-n+5, 0) \le j \le \min(k,4)} \binom{8-j}{j}\binom{2n-k+j-10}{k-j} & \text{if } n > 5 \end{cases}$$
-/
def A258667 (n : ℕ) : ℕ :=
  if h : n ≤ 5 then 0 else
  (Finset.sum (Finset.range n) fun k =>
    let sign : ℤ := if k % 2 = 0 then 1 else -1
    -- Nat.factorial (n - 1 - k) is safe since h implies n > 5 and k < n.
    let fac_term : ℤ := ofNat (Nat.factorial (n - 1 - k))

    sign * fac_term * A258667_inner_sum n k
  ).natAbs

noncomputable def nat_fac_to_real (n : ℕ) : ℝ := (Nat.factorial n : ℝ)

/-- The denominator term $k! (n-1)_k$ represented as a Real number. -/
noncomputable def menage_denom_term (n k : ℕ) : ℝ :=
  let k_fac_R := nat_fac_to_real k
  -- (n-1)_k is the falling factorial. Nat.descFactorial (n-1) k is (n-1)!/(n-1-k)!
  let falling_fac := (Nat.descFactorial (n - 1) k : ℝ)
  k_fac_R * falling_fac

/-- The infinite series part of the asymptotic expansion: $\sum_{k \ge 1} \frac{(-1)^k}{k!(n-1)_k}$. -/
noncomputable def A258667_asymptotic_sum_part (n : ℕ) : ℝ :=
  -- The sum is effectively finite since (n-1)_k is 0 for k >= n.
  Finset.sum (Finset.range n) fun k =>
    if k = 0 then 0
    else
      let denom := menage_denom_term n k
      -- Denominator is non-zero if n >= 1 and 1 <= k < n.
      if denom = 0 then 0
      else ((-1 : ℝ) ^ k) / denom

/-- The proposed asymptotic expression for A258667(n). -/
noncomputable def A258667_asymptotic_term (n : ℕ) : ℝ :=
  if n ≤ 2 then 0 -- Avoid division by zero, irrelevant for n -> infinity
  else
    let n_R : ℝ := n
    let n_fac_R := nat_fac_to_real n
    let prefactor : ℝ := exp (-2) * (n_fac_R / (n_R - 2))
    prefactor * (1 + A258667_asymptotic_sum_part n)

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

lemma inner_sum_zero (n : ℕ) (h : 5 ≤ n) : A258667_inner_sum n 0 = 1 := by
  delta and A258667_inner_sum
  exact (Nat.sub_eq_zero_of_le h).symm▸.trans (add_zero _) ((congr_arg _) ((congr_arg _) (@Nat.choose_zero_right _) ) )

lemma inner_sum_one (n : ℕ) (h : 6 ≤ n) : A258667_inner_sum n 1 = 2 * n - 4 := by
  norm_num[mul_comm, A258667_inner_sum ·]
  exact (.trans (by rw [tsub_eq_zero_of_le h,←Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ, Finset.sum_range_one]) (.trans ( by aesop) (by valid)))

lemma asymp_sum_limit : Tendsto (fun n => A258667_asymptotic_sum_part n) atTop (𝓝 0) := by
  delta A258667_asymptotic_sum_part
  norm_num[ menage_denom_term, true, Finset.sum_ite, false, Finset.filter_ne']
  delta nat_fac_to_real
  rw [←Filter.tendsto_add_atTop_iff_nat 1,funext fun and=>congr_arg₂ _ (Finset.filter_true_of_mem (by simp_all[·.lt_succ,Nat.factorial_ne_zero])) rfl]
  norm_num[Nat.range_succ_eq_Icc_zero,Nat.descFactorial_eq_prod_range,neg_div]
  convert_to (Filter.Tendsto fun and=>∑'x,ite ( 1 ≤ x ∧x ≤and) ((-1)^x/(x !*∏ a ∈.range x,↑(and-a)) : ℝ) 0) _ _
  · simp_all only [← Finset.mem_Icc, if_pos, true,tsum_eq_sum fun and β =>if_neg β,show∀ (n : ℕ),.Ioc 0 (n : ℕ)= Finset.Icc (1) (n : ℕ)by {subsingleton}]
  use((tendsto_tsum_of_dominated_convergence (1:ℝ).summable_pow_div_factorial fun and=>?_) (Filter.eventually_atTop.2 ⟨1,fun A B=>?_⟩)).trans (by rw [tsum_zero])
  · refine match and with|0=>tendsto_const_nhds.congr<|by simp_all | S+1=>.if' (.const_div_atTop (.const_mul_atTop (by positivity) ? _) _) ↑tendsto_const_nhds
    refine ((Filter.tendsto_atTop_mono' _) (@Filter.eventually_atTop.2 ⟨S+1, fun and x =>mod_cast(? _)⟩)) tendsto_natCast_atTop_atTop
    exact (.trans (by constructor) ( Finset.single_le_prod' ↑( ·.sub_pos_of_lt ∘x.trans'.comp (List.mem_range.mp)) (List.mem_range.mpr S.succ_pos)))
  · use fun and=>or_not.elim (if_pos ·▸(@norm_div ℝ _ _ _▸div_le_div₀ (by bound) (by rw [norm_pow, one_pow,norm_neg,norm_one, one_pow]) (by positivity) (mod_cast(?_)))) (if_neg ·▸mod_cast (by bound))
    exact (le_mul_of_one_le_right') ↑( Finset.one_le_prod' ↑( ·.sub_pos_of_lt ∘by valid ∘ Finset.mem_range.1 ) )

lemma asymp_sum_plus_one_limit : Tendsto (fun n => 1 + A258667_asymptotic_sum_part n) atTop (𝓝 1) := by
  delta A258667_asymptotic_sum_part Filter.Tendsto
  norm_num[ menage_denom_term, true, Finset.sum_ite, false, Finset.filter_ne']
  push_cast[nat_fac_to_real,Nat.descFactorial_eq_factorial_mul_choose,←div_div]
  have := (hasSum_nat_add_iff' 1).2 (1:ℝ).summable_pow_div_factorial.hasSum
  replace: (Filter.Tendsto fun and=>∑' (n : ℕ),(-1)^ (n + 1)/( (n + 1)! : ℝ) / (n + 1)! / (and-1).choose (n + 1)) ↑.atTop (𝓝 0)
  · use(((tendsto_tsum_of_dominated_convergence ↑this.summable fun and=>(tendsto_const_div_atTop_nhds_zero_nat _).comp (Filter.tendsto_atTop_atTop.mpr fun and' =>?_)) (Filter.eventually_atTop.mpr ⟨2,?_⟩))).trans (by rw [tsum_zero])
    · use and+and'+2,fun a s=>.trans (?_) (Nat.choose_le_choose _ (by valid: a-1≥and+1+and'))
      use (and').rec bot_le (and.succ.add_succ ·▸lt_add_of_pos_of_le (Nat.choose_pos (by valid)))
    · refine fun and R L=>.trans (norm_div _ _).le ((Nat.eq_zero_or_pos _).elim (by norm_num [·]) (div_le_self (norm_nonneg _)|>.comp (mod_cast ·) ·|>.trans (norm_mul_le_of_le @?_ (by·norm_num))))
      exact (norm_div _ _).trans_le.comp (div_le_self ↑(norm_nonneg _) ↑(mod_cast L.succ.factorial_pos)).trans (by rw [norm_pow, one_pow _,norm_neg _,norm_one, one_pow])
  · use((this.congr' (Filter.eventually_atTop.2 ⟨1,fun A B=>match A with | S+1=>(tsum_eq_sum (s:=.range S) (by simp_all[Nat.succ_le,Nat.choose_eq_zero_of_lt])).trans (? _)⟩)).const_add _).trans (by rw [add_zero])
    exact (symm ((congr_arg₂ _ (Finset.filter_true_of_mem fun and μ=>⟨by positivity, Finset.mem_range_succ_iff.1 (Finset.erase_subset _ _ μ)⟩) rfl).trans (by norm_num[ Finset.sum_range_succ'])))

lemma asymp_sum_equiv_one : IsEquivalent atTop (fun n => 1 + A258667_asymptotic_sum_part n) (fun n => (1 : ℝ)) := by
  norm_num[ A258667_asymptotic_sum_part, Asymptotics.isEquivalent_iff_exists_eq_mul]
  norm_num[ menage_denom_term, false,Pi.mul_def, true, Finset.sum_ite, true, Finset.filter_ne']
  delta nat_fac_to_real
  refine ⟨ _,(((Filter.tendsto_add_atTop_iff_nat 1).1) ?_).const_add (1)|>.trans (by rw [add_zero]),.of_forall fun and=>rfl⟩
  norm_num[neg_div,Finset.filter_true_of_mem,Nat.range_succ_eq_Icc_zero,Nat.descFactorial_eq_prod_range,Nat.factorial_ne_zero]
  show((Filter.Tendsto fun and =>∑ a ∈_, _/ (@_ *∏ a ∈ _,Nat.cast @_)) _ _)
  convert tendsto_tsum_of_dominated_convergence (1:ℝ).summable_pow_div_factorial _ _ using 002
  change _=∑'a,ite ( a ∈ Finset.Ioc 0 (by bound)) ((-1)^a/(a !*∏ a ∈.range a,↑(by bound-a)): ℝ) 0
  simp_all only [ tsum_eq_sum fun and β=>if_neg β, (if_pos)]
  exact(tsum_zero.symm)
  · infer_instance
  · use (if R:0<. then((((Filter.tendsto_add_atTop_iff_nat (by valid)).1) ?_).const_div_atTop _).if' tendsto_const_nhds else (by norm_num[R]))
    refine ((Filter.tendsto_atTop_mono fun and=>mod_cast (Finset.single_le_prod' ( fun and=>by valid ∘ Finset.mem_range.1) (List.mem_range.2 R)).trans' (by valid)) (tendsto_natCast_atTop_atTop)).const_mul_atTop (by positivity)
  · use .of_forall fun and x =>(em _).elim (if_pos ·▸(@norm_div ℝ _ _ _▸div_le_div₀ (by bound) (by simp_all) (by positivity) (mod_cast(le_mul_of_one_le_right') ?_))) (if_neg ·▸mod_cast (by bound))
    refine Finset.one_le_prod' (·.sub_pos_of_lt.comp ( Finset.mem_Ioc.mp (by assumption)).2.trans' ∘ Finset.mem_range.mp)

lemma ratio_identity (n : ℕ) (h : 2 < n) : (n : ℝ) / (n - 2) = 1 + 2 / (n - 2) := by
  rw [ one_add_div (by apply sub_ne_zero.2 (mod_cast h.ne')), sub_add_cancel]

lemma term_two_div_limit :
  Tendsto (fun n : ℕ => (2 : ℝ) / (n - 2)) atTop (𝓝 0) := by
  apply ((tendsto_natCast_atTop_atTop).atTop_add tendsto_const_nhds).const_div_atTop

lemma prefactor_ratio_limit :
  Tendsto (fun n : ℕ => (n : ℝ) / (n - 2)) atTop (𝓝 1) := by
  exact (tendsto_natCast_div_add_atTop ((-2 ) )).congr fun and=>by ·ring

lemma prefactor_frac_equiv :
  IsEquivalent atTop (fun n : ℕ => nat_fac_to_real n / (n - 2)) (fun n => nat_fac_to_real (n - 1)) := by
  simp_rw [nat_fac_to_real, Asymptotics.isEquivalent_iff_exists_eq_mul]
  exact ⟨ _,tendsto_natCast_div_add_atTop (-2),Filter.eventually_atTop.2 ⟨1,fun A B=>by match A with | S+1=>exact (congr_arg (·/_) (Nat.cast_mul _ _)).trans (.trans (by ring!) (mul_right_comm _ _ _))⟩⟩

lemma prefactor_equiv :
  IsEquivalent atTop (fun n : ℕ => exp (-2) * (nat_fac_to_real n / (n - 2))) (fun n => exp (-2) * nat_fac_to_real (n - 1)) := by
  simp_rw [nat_fac_to_real, mul_div, Asymptotics.isEquivalent_iff_exists_eq_mul ·]
  refine ⟨ _, ((tendsto_natCast_div_add_atTop) (-2)),Filter.eventually_atTop.mpr ⟨1,fun R L=>match R with | S+1=>.trans (congr_arg (·/_) (.trans (by rw [ S.factorial_succ,Nat.cast_mul]) (by exact by ring!))) (mul_right_comm _ _ _)⟩⟩

lemma asymp_term_def_eventually :
  ∀ᶠ n in atTop, A258667_asymptotic_term n = exp (-2) * (nat_fac_to_real n / (n - 2)) * (1 + A258667_asymptotic_sum_part n) := by
  simp_rw [mul_assoc, A258667_asymptotic_term, A258667_asymptotic_sum_part]
  exact (Filter.eventually_gt_atTop _).mono fun and(S) =>by rw [mul_assoc, if_neg S.not_ge]

lemma asymp_term_equiv :
  IsEquivalent atTop A258667_asymptotic_term (fun n => exp (-2) * nat_fac_to_real (n - 1)) := by
  delta A258667_asymptotic_term nat_fac_to_real Real.exp
  norm_num[mul_assoc, A258667_asymptotic_sum_part, Asymptotics.isEquivalent_iff_exists_eq_mul, mul_div_assoc _,Complex.exp_re]
  delta menage_denom_term
  delta nat_fac_to_real
  refine ⟨ _,((Filter.tendsto_add_atTop_iff_nat 1).1) ? _,Filter.eventually_atTop.2 ⟨3,fun A B=> (if_neg (by valid)).trans (div_mul_cancel₀ _ (by positivity)).symm⟩⟩
  norm_num[add_sub_assoc, mul_div_mul_left _,.!,Nat.descFactorial_eq_factorial_mul_choose,Nat.factorial_ne_zero,pow_add,neg_div, Finset.sum_range_succ']
  have:Filter.Tendsto (fun p=>∑n ∈.range p,-((-1)^n/( (n + 1)*(n)!*( (n + 1)*(n)!*p.choose (n + 1))):ℝ)) .atTop (𝓝 0)
  · rw [←Filter.tendsto_add_atTop_iff_nat 01]
    use squeeze_zero_norm ( fun and=>norm_sum_le _ _) (( squeeze_zero fun and=>by positivity fun and=>? _) ((tendsto_inverse_atTop_nhds_zero_nat.comp (Filter.tendsto_add_atTop_nat (1))).const_mul (rexp (1)) |>.trans (by simp_all)))
    use(Finset.sum_le_sum fun and Y=>? _).trans (.trans (by rw [ Finset.sum_mul]) (mul_le_mul_of_nonneg_right (Real.sum_le_exp_of_nonneg zero_le_one _) ((inv_nonneg.2 (by bound)))))
    use((norm_neg _).trans (norm_div _ _)).trans_le.comp (div_le_div₀ (by positivity) (by simp_all) (by positivity) (mod_cast(?_))).trans (div_div _ _ _).ge
    apply(mul_le_mul_left' (le_mul_of_one_le_left' (mul_pos and.succ_pos and.factorial_pos)) ( _)).trans'
    exact (mul_right_mono ↑( and.le_induction ↑(by simp_all) (fun R M i=>by nlinarith[(R+1).succ_mul_choose_eq and, R.succ.choose_succ_succ and]) _ (Finset.mem_range_succ_iff.1 Y))).trans (mul_assoc _ _ _|>.trans (mul_left_comm _ _ _)).ge
  · apply((((tendsto_inverse_atTop_nhds_zero_nat.const_add 1).div (tendsto_inverse_atTop_nhds_zero_nat.neg.const_add 1) (by bound)).mul (this.const_add (1))).congr'<|Filter.eventually_atTop.2 ⟨1, _⟩).trans_eq<|by ring
    exact (fun A B=>eq_div_of_mul_eq (by positivity) (.trans (by rw [Pi.div_apply]) (.symm (.trans (by rw [funext fun and=>ite_eq_right_iff.2 (·.symm▸by ring)]) (by field_simp[mul_right_comm])))))

noncomputable def seq_sum (n : ℕ) : ℤ :=
  Finset.sum (Finset.range n) fun k =>
    (if k % 2 = 0 then 1 else -1) * (Nat.factorial (n - 1 - k) : ℤ) * A258667_inner_sum n k

lemma seq_def_eventually :
  ∀ᶠ n in atTop, (A258667 n : ℝ) = |(seq_sum n : ℝ)| := by
  delta and A258667 seq_sum
  exact (Filter.eventually_gt_atTop _).mono fun and(S) =>dif_neg S.not_ge▸.trans (Int.cast_inj.2<|Int.cast_natAbs _) ↑(Int.cast_abs)

noncomputable def seq_sum_ratio (n : ℕ) : ℝ :=
  (seq_sum n : ℝ) / nat_fac_to_real (n - 1)

noncomputable def seq_sum_ratio_term (n k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ k) * (A258667_inner_sum n k : ℝ) / (Nat.descFactorial (n - 1) k : ℝ)

lemma seq_sum_real_def (n : ℕ) :
  (seq_sum n : ℝ) = Finset.sum (Finset.range n) fun k =>
    (if k % 2 = 0 then (1 : ℝ) else -1) * (Nat.factorial (n - 1 - k) : ℝ) * (A258667_inner_sum n k : ℝ) := by
  push_cast[seq_sum, A258667_inner_sum, false, (by cases·.mod_two_eq_zero_or_one with ·norm_num [Nat.even_iff,Nat.odd_iff, *]:∀ (x : ℕ),ite (x % 2 =0) @1 (-1 :ℝ)=(-1) ^ x), Finset.mul_sum]
  constructor

lemma seq_sum_ratio_term_eq (n k : ℕ) (h : k < n) :
  ((if k % 2 = 0 then (1 : ℝ) else -1) * (Nat.factorial (n - 1 - k) : ℝ) * (A258667_inner_sum n k : ℝ)) / nat_fac_to_real (n - 1) = seq_sum_ratio_term n k := by
  push_cast[seq_sum_ratio_term, A258667_inner_sum,nat_fac_to_real, (by cases k.mod_two_eq_zero_or_one with simp_all[k.even_iff,k.odd_iff]:ite (k % 2 =0) (1 : ℝ) (-1)=(-1)^k),mul_assoc]
  rw [←Nat.factorial_mul_descFactorial (k.le_sub_one_of_lt h),Nat.cast_mul,mul_left_comm, mul_div_mul_left _ _ (by positivity)]

lemma seq_sum_ratio_sum_def (n : ℕ) :
  seq_sum_ratio n = Finset.sum (Finset.range n) fun k => seq_sum_ratio_term n k := by
  rw [← Finset.sum_range_reflect,seq_sum_ratio, Eq.comm]
  push_cast [seq_sum_ratio_term, false,seq_sum, false,nat_fac_to_real]
  rw [← Finset.sum_range_reflect, Finset.sum_congr rfl fun R M=>.trans (by rw [Nat.descFactorial_eq_div (Nat.sub_le _ _),Nat.sub_sub_self (R.le_sub_one_of_lt (by simp_all))]) ? _, Finset.sum_div]
  cases R.mod_two_eq_zero_or_one with push_cast[*, R.even_iff,eq_self,mul_right_comm,neg_one_pow_eq_ite,div_div_eq_mul_div,Nat.sub_le,Nat.factorial_dvd_factorial]

lemma seq_sum_ratio_term_zero_of_ge (n k : ℕ) (h : n ≤ k) :
  seq_sum_ratio_term n k = 0 := by
  rw [←eq_comm,seq_sum_ratio_term]
  cases n with simp_all[Nat.descFactorial_of_lt ∘h.trans',A258667_inner_sum]

lemma seq_sum_ratio_tsum (n : ℕ) :
  seq_sum_ratio n = ∑' k, seq_sum_ratio_term n k := by
  delta seq_sum_ratio_term seq_sum_ratio
  push_cast [seq_sum, A258667_inner_sum,nat_fac_to_real, false,Nat.descFactorial_eq_factorial_mul_choose]
  rw[tsum_eq_sum (s:=.range n) (by cases n with simp_all[Nat.succ_le,Nat.choose_eq_zero_of_lt]), Finset.sum_div, Finset.sum_congr rfl fun and β=>?_]
  exact (symm (.trans (by rw [Nat.cast_choose ℝ (and.le_sub_one_of_lt<|by simp_all),mul_div, mul_div_mul_left _ _ (by positivity),div_div_eq_mul_div,neg_one_pow_eq_ite]) (by grind)))

lemma seq_sum_ratio_term_limit (k : ℕ) :
  Tendsto (fun n : ℕ => seq_sum_ratio_term n k) atTop (𝓝 (((-2 : ℝ) ^ k) / (Nat.factorial k : ℝ))) := by
  delta seq_sum_ratio_term Filter.Tendsto
  push_cast[Nat.descFactorial_eq_prod_range, mul_div_assoc, A258667_inner_sum]
  push_cast[Int.ofNat_eq_coe, max_eq_right zero_le',Nat.choose_eq_descFactorial_div_factorial, mul_div_assoc,Nat.cast_div,Nat.factorial_dvd_descFactorial, Finset.sum_div]
  push_cast[div_right_comm _ ((k- _)! : ℝ), ← Finset.prod_div_distrib, two_mul,Nat.descFactorial_eq_prod_range, add_assoc]
  rw [←Filter.map_congr.comp (Filter.eventually_ge_atTop _).mono fun and β =>by rw [tsub_eq_zero_of_le β]]
  rw [←Filter.map_congr (Filter.eventually_atTop.2 ⟨k+10,fun A B=>by rw [←Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ']⟩)]
  use((((tendsto_finset_sum _) fun and x =>((Filter.tendsto_add_atTop_iff_nat (k+10)).1 ?_).const_mul _).add ?_).const_mul _).trans (by rw [ Finset.sum_eq_zero fun and x =>mul_zero _,zero_add, mul_div_cancel₀ _ (by·hint)])
  · push_cast[k.sub_add_cancel ((List.mem_range.1 x).trans_le (by bound))▸ Finset.prod_range_add _ _ _,←add_assoc, ← Finset.prod_div_distrib]
    push_cast[lt_min_iff, Finset.prod_range_succ',←div_div, add_assoc,← Finset.prod_div_distrib, Finset.mem_range]at*
    use(((bdd_le_mul_tendsto_zero' (∏ a ∈.range (k- (and + 1)), 2) (.of_forall fun and=>((abs_of_nonneg (by positivity)).trans_le) ?_) (tendsto_inverse_atTop_nhds_zero_nat.comp ?_)).div_const _).trans (by rw [zero_div]))
    · use(div_le_self (by positivity) (.trans (by norm_num) ( Finset.prod_le_prod (fun a s=>zero_le_one) fun and=>mod_cast (by valid ∘ Finset.mem_range.1)))).trans ( Finset.prod_le_prod (by bound) ? _)
      refine fun and=>div_le_of_le_mul₀ (by·bound) (2).cast_nonneg ∘mod_cast (by valid ∘ Finset.mem_range.mp)
    · exact (Filter.tendsto_atTop_mono (by valid)) ↑le_rfl
  · have R M:=((tendsto_const_div_atTop_nhds_zero_nat (k+10+M:ℝ)).const_sub 2).div ((tendsto_const_div_atTop_nhds_zero_nat (1+M:ℝ)).const_sub (1)) (by simp_all)
    use((((tendsto_finset_prod (.range k) (fun a s=>R a)).div_const (k : ℕ)!).congr' (Filter.eventually_atTop.2 ⟨k+10+ (k + 1),fun a s=>?_⟩))).trans (by norm_num[div_right_comm _ (( _)! : ℝ),←div_pow])
    simp_all[div_div_eq_mul_div, sub_sub, two_mul, (by exact fun and=>by valid ∘ Finset.mem_range.1 : ∀x ∈ Finset.range k, a+a-(k+10)≥x∧k ≤ a-1∧k+10 ≤ a+a∧0<a∧a≠0),sub_div']
    simp_all[div_div_eq_mul_div, sub_sub, sub_div',two_mul, (by valid: 1 ≤ a∧k+10 ≤ a+a∧a≠0),(Finset.mem_range.1 _).le.trans (by valid: a-1≥k)]

lemma hasSum_exp_minus_two :
  HasSum (fun k : ℕ => ((-2 : ℝ) ^ k) / (Nat.factorial k : ℝ)) (exp (-2)) := by
  have:= Real.exp_eq_exp_ℝ
  simp_rw [this,NormedSpace.expSeries_div_hasSum_exp]

noncomputable def bound_seq (k : ℕ) : ℝ :=
  350 * (3 : ℝ) ^ k / (Nat.factorial k : ℝ)

lemma bound_seq_summable : Summable bound_seq := by
  show Summable fun and=>(id _)
  push_cast [id, (@3:ℝ).summable_pow_div_factorial.mul_left, mul_div_assoc]

lemma k_sub_succ_eq (k j : ℕ) : k - (j + 1) = k - j - 1 := by omega

lemma choose_sub_one_le_choose_add_one (a b : ℕ) :
  Nat.choose a (b - 1) ≤ Nat.choose (a + 1) b := by
  exact (b.casesOn ((by simp_all ) ) fun and=>le_self_add)

lemma choose_le_choose_add_step (m k j : ℕ)
  (ih : Nat.choose (m + 1) (k - j) ≤ Nat.choose (m + 1 + j) k)
  (h2 : Nat.choose m (k - j - 1) ≤ Nat.choose (m + 1) (k - j)) :
  Nat.choose m (k - (j + 1)) ≤ Nat.choose (m + j + 1) k := by
  apply m.succ_add j▸ h2.trans ih

lemma choose_le_choose_add (m k j : ℕ) :
  Nat.choose m (k - j) ≤ Nat.choose (m + j) k := by
  use if a:_ then j.rec (by bound) ?_ k a else(m.choose_eq_zero_of_lt (not_le.1 a))▸bot_le
  exact fun and a s R=>s.casesOn (by norm_num) (·.succ_sub_succ_eq_sub and▸le_add_right (by apply_rules))

lemma desc_factorial_le_of_le_step (A B k : ℕ) (ih : Nat.descFactorial A k ≤ 3^k * Nat.descFactorial B k) (h_step : A - k ≤ 3 * (B - k)) :
  Nat.descFactorial A (k + 1) ≤ 3^(k + 1) * Nat.descFactorial B (k + 1) := by
  exact (Nat.mul_le_mul h_step ih).trans_eq (B.descFactorial_succ k▸by(((ring))))

lemma desc_factorial_le_of_le (A B k : ℕ) (h3 : ∀ i < k, A - i ≤ 3 * (B - i)) :
  Nat.descFactorial A k ≤ 3^k * Nat.descFactorial B k := by
  simp_all only [← Fin.prod_const,← Finset.prod_mul_distrib, true, implies_true,Nat.descFactorial_eq_prod_range, Finset.prod_le_prod', Finset.mem_range]
  exact ( Finset.prod_le_prod' (h3 · ∘by·norm_num ) ).trans (by rw [ Finset.prod_mul_distrib, Finset.prod_range])

lemma desc_factorial_bound_nat (n k : ℕ) (hk : k < n) :
  Nat.descFactorial (2 * n - k) k ≤ 3^k * Nat.descFactorial (n - 1) k := by
  apply desc_factorial_le_of_le
  intro i hi
  omega

lemma term1_bound (j : ℕ) :
  Nat.choose (8 - j) j ≤ 70 := by
  match j with|0|1|2|3|4|5|6|7 | (8) => decide | S+9 =>push_cast [tsub_eq_zero_of_le,Nat.choose]

lemma inner_sum_bound_choose (n k : ℕ) :
  (A258667_inner_sum n k : ℝ) ≤ 350 * (Nat.choose (2 * n - k) k : ℝ) := by
  push_cast[two_mul, A258667_inner_sum]
  trans∑ a ∈.Icc 0 (4 : ℕ),(8-a).choose a*(n+ n- k).choose k
  · use(Finset.sum_le_sum fun a s=>mul_le_mul_of_nonneg_left (Nat.cast_le.2 ? _) (by bound)).trans ( Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc bot_le (by bound)) (by bound))
    simp_all
    match a with|0|1|2|3|4=>?_
    · use Nat.choose_le_choose k<|by valid
    · match k with | S+1=>exact (Nat.choose_le_choose S (by valid)).trans (le_self_add.trans (.trans (Nat.choose_succ_left _ _ S.succ_pos).ge (Nat.choose_le_choose _ (by valid))))
    · use(by valid:n+n-k=n+n+2-(k+10)+8)▸match k with | S+2=>le_add_right<|le_add_right (Nat.choose_le_choose S (by valid))
    · push_cast[ (by valid:n+n-k=n+n-(k+7)+7),Nat.choose]
      match k with | S+3=>exact (Nat.choose_le_choose @_ (by repeat constructor)).trans (le_self_add.trans (le_self_add.trans (le_self_add)))
    match k with | S+4=>?_
    simp_all![ (by valid:n+n-(S+4)=n+n-(S+10)+6),le_add_right]
    linarith
  · exact ( Finset.sum_mul _ _ _).ge.trans (mul_le_mul_of_nonneg_right (by·norm_cast) ( (by(bound))))

lemma inner_sum_nonneg (n k : ℕ) : 0 ≤ (A258667_inner_sum n k : ℝ) := by
  delta and A258667_inner_sum
  exact (Int.cast_le.mpr.comp Finset.sum_nonneg' fun and=>by constructor).trans' (by ((norm_num)))

lemma seq_sum_ratio_term_abs (n k : ℕ) :
  |seq_sum_ratio_term n k| = (A258667_inner_sum n k : ℝ) / (Nat.descFactorial (n - 1) k : ℝ) := by
  delta seq_sum_ratio_term A258667_inner_sum
  rw [mul_div_assoc, abs_mul, abs_neg_one_pow, one_mul, abs_of_nonneg (by exact div_nonneg (Int.cast_le.2 (Finset.sum_nonneg' fun and=>by constructor) |>.trans' (by norm_num)) (by bound))]

lemma choose_real_eq (m k : ℕ) :
  (Nat.choose m k : ℝ) = (Nat.descFactorial m k : ℝ) / (Nat.factorial k : ℝ) := by
  simp_all[m.descFactorial_eq_factorial_mul_choose,(k.factorial_ne_zero)]

lemma seq_sum_ratio_term_bound_lt (n k : ℕ) (hk : k < n) :
  |seq_sum_ratio_term n k| ≤ bound_seq k := by
  rw [seq_sum_ratio_term_abs n k]
  have h_inner := inner_sum_bound_choose n k
  have h_choose := choose_real_eq (2 * n - k) k
  have h_desc : (Nat.descFactorial (2 * n - k) k : ℝ) ≤ (3 : ℝ)^k * (Nat.descFactorial (n - 1) k : ℝ) := by
    exact_mod_cast desc_factorial_bound_nat n k hk
  have h_bound_seq : bound_seq k = 350 * (3 : ℝ)^k / (Nat.factorial k : ℝ) := rfl
  refine (by assumption▸div_le_of_le_mul₀ (by bound) (by positivity) (h_inner.trans (h_choose▸by linear_combination h_desc * ↑350/↑ (k : ℕ)!)))

lemma seq_sum_ratio_term_bound_ge (n k : ℕ) (hk : ¬(k < n)) :
  |seq_sum_ratio_term n k| ≤ bound_seq k := by
  delta bound_seq seq_sum_ratio_term
  cases n with|zero=>norm_num[le_of_lt, A258667_inner_sum,k.factorial_pos]|succ=>exact (.trans (by rw [Nat.descFactorial_of_lt (by valid),Nat.cast_zero,div_zero,abs_zero]) (by positivity))

lemma seq_sum_ratio_term_bound (n k : ℕ) :
  |seq_sum_ratio_term n k| ≤ bound_seq k := by
  by_cases hk : k < n
  · exact seq_sum_ratio_term_bound_lt n k hk
  · exact seq_sum_ratio_term_bound_ge n k hk

lemma tsum_limit_eq_exp_minus_two :
  (∑' k, ((-2 : ℝ) ^ k) / (Nat.factorial k : ℝ)) = exp (-2) := by
  rw [←eq_comm,Real.exp_eq_exp_ℝ]
  simp_rw [NormedSpace.exp_eq_tsum_div]

lemma seq_sum_ratio_limit_tsum :
  Tendsto (fun n : ℕ => ∑' k, seq_sum_ratio_term n k) atTop (𝓝 (∑' k, ((-2 : ℝ) ^ k) / (Nat.factorial k : ℝ))) := by
  have h1 : ∀ n k, ‖seq_sum_ratio_term n k‖ ≤ bound_seq k := by
    intro n k
    exact seq_sum_ratio_term_bound n k
  have h2 : Summable bound_seq := bound_seq_summable
  have h3 : ∀ k, Tendsto (fun n => seq_sum_ratio_term n k) atTop (𝓝 (((-2 : ℝ) ^ k) / (Nat.factorial k : ℝ))) := seq_sum_ratio_term_limit
  exact tendsto_tsum_of_dominated_convergence h2 h3 (Filter.Eventually.of_forall h1)

lemma seq_sum_ratio_limit :
  Tendsto (fun n : ℕ => seq_sum_ratio n) atTop (𝓝 (exp (-2))) := by
  have h1 : seq_sum_ratio = fun n => ∑' k, seq_sum_ratio_term n k := funext seq_sum_ratio_tsum
  rw [h1]
  have h3 : (∑' k, ((-2 : ℝ) ^ k) / (Nat.factorial k : ℝ)) = exp (-2) := tsum_limit_eq_exp_minus_two
  rw [← h3]
  exact seq_sum_ratio_limit_tsum

lemma seq_sum_equiv :
  IsEquivalent atTop (fun n : ℕ => (seq_sum n : ℝ)) (fun n => exp (-2) * nat_fac_to_real (n - 1)) := by
  have h1 : Tendsto (fun n => (seq_sum n : ℝ) / nat_fac_to_real (n - 1)) atTop (𝓝 (exp (-2))) := seq_sum_ratio_limit
  push_cast only [nat_fac_to_real, Asymptotics.isEquivalent_iff_exists_eq_mul]at *
  exact ⟨ _,div_self (Real.exp_ne_zero _)▸h1.div_const _,.of_forall fun and=>((div_eq_iff (by positivity)).1 ((div_mul_cancel₀ _) (by norm_num)).symm).trans (mul_assoc _ _ _)⟩

lemma exp_fac_pos (n : ℕ) : 0 < exp (-2) * nat_fac_to_real (n - 1) := by
  rw [←mul_comm,nat_fac_to_real]
  convert←mul_pos.comp Nat.cast_pos.mpr (n-1).factorial_pos (@Real.exp_pos ( -2))

lemma seq_sum_abs_equiv :
  IsEquivalent atTop (fun n : ℕ => |(seq_sum n : ℝ)|) (fun n => exp (-2) * nat_fac_to_real (n - 1)) := by
  have h1 := seq_sum_equiv
  simp_rw [nat_fac_to_real, Asymptotics.isEquivalent_iff_exists_eq_mul] at *
  exact h1.elim fun and⟨A, B⟩=>⟨_, A.norm.trans (by rw [norm_one]),B.mono fun and x =>(congr_arg abs x).trans ((norm_mul _ _).trans (congr_arg _ (Real.norm_of_nonneg (by positivity))))⟩

lemma seq_equiv :
  IsEquivalent atTop (fun n : ℕ => (A258667 n : ℝ)) (fun n => exp (-2) * nat_fac_to_real (n - 1)) := by
  have h1 := seq_def_eventually
  have h2 := seq_sum_abs_equiv
  simp_rw [mul_comm, Asymptotics.isEquivalent_iff_exists_eq_mul]at *
  apply h2.imp fun and =>.imp fun and =>h1.mp.comp ( ·.mono fun and R M=>M.trans R)

-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : IsEquivalent atTop (fun n : ℕ => (A258667 n : ℝ)) A258667_asymptotic_term := by
  -- EVOLVE-BLOCK-START
  have h1 := seq_equiv
  have h2 := asymp_term_equiv
  exact Asymptotics.IsEquivalent.trans h1 (Asymptotics.IsEquivalent.symm h2)
  -- EVOLVE-BLOCK-END
