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




open BigOperators LinearRecurrence

/--
The sequence $b_n$ such that $A227582(n) = b_{n-1}$ for $n \ge 1$.
This is the 0-indexed solution to the linear recurrence in $\mathbb{Z}$.
-/
def A227582_base (n : ℕ) : ℤ :=
  let order := 7
  -- Coefficients $c_i$ for the recurrence $u_{n+7} = \sum_{i=0}^6 c_i u_{n+i}$.
  -- This corresponds to the OEIS signature $(2, -1, 0, 0, 1, -2, 1)$ which means $c_i = s_{7-i}$.
  let coeffs : Fin order → ℤ := ![1, -2, 1, 0, 0, -1, 2]
  -- Initial values $a_0$ through $a_6$. These are {2, 7, 14, 23, 35, 50, 67}.
  let init : Fin order → ℤ := ![2, 7, 14, 23, 35, 50, 67]
  let E : LinearRecurrence ℤ := { order := order, coeffs := coeffs }
  E.mkSol init n

/--
A227582: Expansion of $(2+3*x+2*x^2+2*x^3+3*x^4+x^5-x^6)/(1-2x+x^2-x^5+2*x^6-x^7)$.
The sequence is 1-indexed in OEIS, so $a(n)$ is the $(n-1)$-th term of the 0-indexed solution.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : 0 < n then
    (A227582_base (n - 1)).toNat
  else
    0

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
lemma a_val (n : ℕ) (hn : 0 < n) : a n = (6 * n^2 + 6 * n - 1) / 5 := by
  delta a
  delta A227582_base
  refine(dif_pos hn▸((congr_arg _) (n.sub_add_cancel hn▸(n-1).strongRec fun and x =>.trans (by rw [LinearRecurrence.mkSol]) ?_)).trans (Int.toNat_natCast _))
  refine match and with|0|1|2|3|4|5|6=>rfl | S+7=>.trans ( Fintype.sum_congr _ _ fun and=>congr_arg @_ (x _ (by (fin_omega)))) ((symm) ? _)
  norm_num [ Finset.sum, mul_add,add_sq]
  grind

noncomputable def x_seq (n : ℕ) : ℝ :=
  2 * (harmonic n : ℝ) - (harmonic (n * n + n - 1) : ℝ) - Real.eulerMascheroniConstant

lemma log_taylor_lower_6 (x : ℝ) (hx : 0 ≤ x) :
  x - x^2 / 2 + x^3 / 3 - x^4 / 4 + x^5 / 5 - x^6 / 6 ≤ Real.log (1 + x) := by
  have R M:=((((hasDerivAt_id' M).sub ((hasDerivAt_pow (2) (M :ℝ)).div_const 2)).add ((hasDerivAt_pow (3) M).div_const (3))).sub ((hasDerivAt_pow 4 M).div_const 4))
  have R M:=(((R M).add ((hasDerivAt_pow 5 M).div_const 5)).sub ((hasDerivAt_pow 06 M).div_const 6)).sub ∘((hasDerivAt_id' M).const_add 1).log
  use sub_nonpos.1 (hx.eq_or_lt.elim (by bound) (exists_hasDerivAt_eq_slope _ _ · ↑(HasDerivAt.continuousOn (R · ∘ (by (linarith[·.1]))) ) (R · ∘ (by linarith[·.1]))|>.elim (@? _) ) )
  exact (fun A B=>not_lt.1 fun and=>(B.2▸sub_neg.2 ((lt_div_iff₀ (by linear_combination B.1.1)).2 (by linear_combination pow_pos B.1.1 6))).asymm (by norm_num[*]))

lemma log_taylor_upper_5 (x : ℝ) (hx : 0 ≤ x) :
  Real.log (1 + x) ≤ x - x^2 / 2 + x^3 / 3 - x^4 / 4 + x^5 / 5 := by
  have R M:=((((hasDerivAt_id' M).sub ((hasDerivAt_pow (2) (M:ℝ)).div_const 2)).add ((hasDerivAt_pow (3) M).div_const (3))).sub ((hasDerivAt_pow 4 M).div_const 4))
  have R M α :=(((hasDerivAt_id' M).const_add (1:ℝ)).log α).sub ((R M).add ((hasDerivAt_pow 05 M).div_const 05))
  refine hx.eq_or_lt.elim (by bound) (exists_hasDerivAt_eq_slope _ _ · ↑(HasDerivAt.continuousOn (R · ∘ (by. (linarith![·.1]))) ) (R · ∘ (by linarith![·.1]))|>.elim fun and x =>? _)
  use not_lt.mp fun and' =>(x.2▸sub_neg.mpr.comp (div_lt_iff₀ (by linear_combination x.1.1)).mpr (by linear_combination pow_pos x.1.1 5)).asymm (by norm_num[*])

lemma log_taylor_upper_7 (x : ℝ) (hx : 0 ≤ x) :
  Real.log (1 + x) ≤ x - x^2 / 2 + x^3 / 3 - x^4 / 4 + x^5 / 5 - x^6 / 6 + x^7 / 7 := by
  have R M:=((((hasDerivAt_id' M).sub ((hasDerivAt_pow (2) (M:ℝ)).div_const 2)).add ((hasDerivAt_pow (3) M).div_const (3))).sub ((hasDerivAt_pow 4 M).div_const 4))
  have R M α :=(((hasDerivAt_id' M).const_add (1:ℝ)).log α).sub ((((R M).add ((hasDerivAt_pow 5 M).div_const 5)).sub ((hasDerivAt_pow 06 M).div_const 6)))
  have R M α :=(R M α).sub ((hasDerivAt_pow (@7) M).div_const 07)
  use sub_le_iff_le_add'.1 (hx.eq_or_lt.elim (by bound) (exists_hasDerivAt_eq_slope _ _ · (HasDerivAt.continuousOn (R · ∘ (by linarith[·.1]))) (R · ∘ (by bound[·.1]))|>.elim) ?_)
  refine fun and⟨⟨A, B⟩,H⟩=>not_lt.1 fun and' =>(H▸sub_neg.2 (sub_lt_iff_lt_add.2 ((div_lt_iff₀ (by linear_combination A)).2 (by linear_combination pow_pos A 7)))).asymm (by norm_num[*, A.trans])

noncomputable def P_lower (n : ℝ) : ℝ := 1 / (2 * n) - 1 / (12 * n^2) + 1 / (120 * n^4) - 1 / (252 * n^6)

lemma log_taylor_lower_12 (x : ℝ) (hx : 0 ≤ x) :
  x - x^2 / 2 + x^3 / 3 - x^4 / 4 + x^5 / 5 - x^6 / 6 + x^7 / 7 - x^8 / 8 + x^9 / 9 - x^10 / 10 + x^11 / 11 - x^12 / 12 ≤ Real.log (1 + x) := by have R M:=((((hasDerivAt_id' M).sub ((hasDerivAt_pow (2) (M:ℝ)).div_const 2)).add ((hasDerivAt_pow (3) M).div_const (3))).sub ((hasDerivAt_pow 4 M).div_const 4))
                                                                                                                                                 have R M := ( (R M).add ((hasDerivAt_pow 5 M).div_const 5)).sub ((hasDerivAt_pow 6 M).div_const 6)|>.add ((hasDerivAt_pow 07 M).div_const @7)
                                                                                                                                                 have R M:=(((R M).sub ((hasDerivAt_pow 08 M).div_const 08)).add ((hasDerivAt_pow (@9) M).div_const @9 ) ).sub ((hasDerivAt_pow 10 M).div_const 010)
                                                                                                                                                 replace R M:=(((R M).add ((hasDerivAt_pow 11 M).div_const 11)).sub ((hasDerivAt_pow 12 M).div_const 12)).sub ∘((hasDerivAt_id M).const_add 1).log
                                                                                                                                                 refine sub_nonpos.mp ((antitoneOn_of_deriv_nonpos (convex_Ici _) ↑(HasDerivAt.continuousOn (R · ∘ (by linarith![·.out]))) ?_ ?_ (by·norm_num) (hx) hx).trans (by (norm_num)))
                                                                                                                                                 · apply fun and x =>(R and (by linarith![(interior_subset x).out])).differentiableAt.differentiableWithinAt
                                                                                                                                                 · exact (fun a s=>match interior_subset s |>.out with | S=>(R a (by linarith!)).deriv▸sub_nonpos.2 ((le_div_iff₀ (by linarith!)).2 (by nlinarith![pow_nonneg S 5,pow_nonneg S 6,pow_nonneg S 7])))
noncomputable def P_upper (n : ℝ) : ℝ := 1 / (2 * n) - 1 / (12 * n^2) + 1 / (60 * n^4)

noncomputable def A_seq (n : ℕ) : ℝ := (harmonic n : ℝ) - Real.log n - P_lower n
noncomputable def B_seq (n : ℕ) : ℝ := (harmonic n : ℝ) - Real.log n - P_upper n

lemma gamma_tendsto : Filter.Tendsto (fun (n : ℕ) => (harmonic n : ℝ) - Real.log n) Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  convert Real.tendsto_harmonic_sub_log

lemma P_lower_tendsto : Filter.Tendsto (fun n : ℕ => P_lower n) Filter.atTop (nhds 0) := by delta and P_lower Filter.Tendsto
                                                                                            have := (tendsto_const_div_atTop_nhds_zero_nat (@1/2) ).sub ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left (@1/12)).tendsto_atTop_zero
                                                                                            apply(((this.add ((hasSum_zeta_four.mul_left (1/120)).summable).tendsto_atTop_zero).sub ((hasSum_zeta_nat three_ne_zero).mul_left (1/252)).summable.tendsto_atTop_zero).congr fun and=>by ring).trans_eq (by norm_num only)
lemma P_upper_tendsto : Filter.Tendsto (fun n : ℕ => P_upper n) Filter.atTop (nhds 0) := by delta and P_upper Filter.Tendsto
                                                                                            apply((((tendsto_natCast_atTop_atTop.const_mul_atTop (by simp_all)).const_div_atTop _).sub (((Real.summable_nat_pow_inv.2 (by decide)).mul_left _).congr fun and=>div_div _ _ _).tendsto_atTop_zero).add _).trans (by rw [sub_self, zero_add])
                                                                                            apply ((Filter.tendsto_pow_atTop four_ne_zero).comp ↑(tendsto_natCast_atTop_atTop)).const_mul_atTop (by simp_all) |>.const_div_atTop

lemma A_seq_tendsto : Filter.Tendsto A_seq Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  have h : A_seq = fun n => ((harmonic n : ℝ) - Real.log n) - P_lower n := rfl
  rw [h]
  have h1 := gamma_tendsto
  have h2 := P_lower_tendsto
  have h3 : Real.eulerMascheroniConstant = Real.eulerMascheroniConstant - 0 := by ring
  rw [h3]
  exact Filter.Tendsto.sub h1 h2

lemma B_seq_tendsto : Filter.Tendsto B_seq Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  have h : B_seq = fun n => ((harmonic n : ℝ) - Real.log n) - P_upper n := rfl
  rw [h]
  have h1 := gamma_tendsto
  have h2 := P_upper_tendsto
  have h3 : Real.eulerMascheroniConstant = Real.eulerMascheroniConstant - 0 := by ring
  rw [h3]
  exact Filter.Tendsto.sub h1 h2

lemma A_seq_anti_step (n : ℕ) (hn : 2 ≤ n) :
  P_lower n - P_lower (n + 1) + 1 / (n + 1 : ℝ) ≤ (1 / n : ℝ) - (1 / n : ℝ)^2 / 2 + (1 / n : ℝ)^3 / 3 - (1 / n : ℝ)^4 / 4 + (1 / n : ℝ)^5 / 5 - (1 / n : ℝ)^6 / 6 + (1 / n : ℝ)^7 / 7 - (1 / n : ℝ)^8 / 8 + (1 / n : ℝ)^9 / 9 - (1 / n : ℝ)^10 / 10 + (1 / n : ℝ)^11 / 11 - (1 / n : ℝ)^12 / 12 := by norm_num(config := {singlePass:=1}) [P_lower, sub_add]
                                                                                                                                                                                                                                                                                                      field_simp
                                                                                                                                                                                                                                                                                                      nlinarith only [pow_three ((n-1)^2 : ℝ),pow_three ((n^2-1)^2 : ℝ),pow_three ((n^3-n)^2 : ℝ),pow_three ((n^4-n^3)^2 : ℝ),show (n : ℝ)≥2by simp_all]

lemma B_seq_mono_step (n : ℕ) (hn : 2 ≤ n) :
  (1 / n : ℝ) - (1 / n : ℝ)^2 / 2 + (1 / n : ℝ)^3 / 3 - (1 / n : ℝ)^4 / 4 + (1 / n : ℝ)^5 / 5 - (1 / n : ℝ)^6 / 6 + (1 / n : ℝ)^7 / 7 ≤ P_upper n - P_upper (n + 1) + 1 / (n + 1 : ℝ) := by norm_num[P_upper, sub_add ·]
                                                                                                                                                                                            field_simp
                                                                                                                                                                                            nlinarith only [pow_three ((n-1)^2 : ℝ),pow_three ((n^2-1)^2 : ℝ), (by norm_cast: (2 : ℝ) ≤ n)]

lemma A_seq_anti (n : ℕ) (hn : 2 ≤ n) : A_seq (n + 1) ≤ A_seq n := by
  unfold A_seq
  have h_step := A_seq_anti_step n hn
  have h_pos : 0 ≤ 1 / (n : ℝ) := by positivity
  have h_log := log_taylor_lower_12 (1 / (n : ℝ)) h_pos
  have h_H : (harmonic (n + 1) : ℝ) - harmonic n = 1 / (n + 1 : ℝ) := by norm_num[harmonic_succ]
  have h_ln : Real.log (n + 1) - Real.log n = Real.log (1 + 1 / (n : ℝ)) := by rw [← Real.log_div (by ·norm_cast) (mod_cast (by valid)),one_add_div (mod_cast (by valid))]
  exact (.trans (by rw [n.cast_succ]) (by ·linear_combination h_step.trans h_log-h_ln +h_H))

lemma B_seq_mono (n : ℕ) (hn : 2 ≤ n) : B_seq n ≤ B_seq (n + 1) := by
  unfold B_seq
  have h_step := B_seq_mono_step n hn
  have h_log := log_taylor_upper_7 (1 / (n : ℝ)) (by positivity)
  have h_H : (harmonic (n + 1) : ℝ) - harmonic n = 1 / (n + 1 : ℝ) := by zify [harmonic_succ, one_div, true,add_sub_cancel_left]
  have h_ln : Real.log (n + 1) - Real.log n = Real.log (1 + 1 / (n : ℝ)) := by rw [← Real.log_div (by norm_cast) (mod_cast (by valid)),one_add_div (mod_cast (by valid))]
  refine (@Nat.cast_succ ℝ _ _).symm▸by·linear_combination h_log.trans h_step-h_H +h_ln

lemma antitone_of_tendsto {f : ℕ → ℝ} {L : ℝ} {N : ℕ}
  (h_tendsto : Filter.Tendsto f Filter.atTop (nhds L))
  (h_anti : ∀ n ≥ N, f (n + 1) ≤ f n) (n : ℕ) (hn : N ≤ n) : L ≤ f n := by exact (le_of_tendsto (by assumption)) (Filter.eventually_atTop.mpr (by use (n : ℕ), n.le_induction le_rfl ↑(.trans ∘h_anti · ∘hn.trans)))

lemma monotone_of_tendsto {f : ℕ → ℝ} {L : ℝ} {N : ℕ}
  (h_tendsto : Filter.Tendsto f Filter.atTop (nhds L))
  (h_mono : ∀ n ≥ N, f n ≤ f (n + 1)) (n : ℕ) (hn : N ≤ n) : f n ≤ L := by exact (ge_of_tendsto (by assumption)) (Filter.eventually_atTop.mpr (by use (n : ℕ), n.le_induction (by valid) fun and μ =>(h_mono and (by valid)).trans'))

noncomputable def E_seq (n : ℕ) : ℝ := (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant

lemma E_seq_lower (n : ℕ) (hn : 2 ≤ n) : P_lower n ≤ E_seq n := by
  have h_anti : ∀ k ≥ 2, A_seq (k + 1) ≤ A_seq k := A_seq_anti
  have h_lim : Real.eulerMascheroniConstant ≤ A_seq n := antitone_of_tendsto A_seq_tendsto h_anti n hn
  unfold A_seq at h_lim
  unfold E_seq
  linarith

lemma E_seq_upper (n : ℕ) (hn : 2 ≤ n) : E_seq n ≤ P_upper n := by
  have h_mono : ∀ k ≥ 2, B_seq k ≤ B_seq (k + 1) := B_seq_mono
  have h_lim : B_seq n ≤ Real.eulerMascheroniConstant := monotone_of_tendsto B_seq_tendsto h_mono n hn
  unfold B_seq at h_lim
  unfold E_seq
  linarith

lemma x_seq_eq (n : ℕ) (hn : 2 ≤ n) :
  x_seq n = 2 * E_seq n - E_seq (n * n + n - 1) - Real.log (1 + (n - 1 : ℝ) / (n * n : ℝ)) := by delta E_seq x_seq
                                                                                                 exact (symm (.trans (by rw [Nat.cast_pred (by valid),Nat.cast_add, one_add_div (by positivity),n.cast_mul,add_sub,Real.log_div (sub_ne_zero.2 (mod_cast (by valid))) (by positivity),Real.log_mul fun and=>by simp_all fun and=>by simp_all]) (by group)))

lemma x_seq_bounds_step (n : ℕ) (hn : 2 ≤ n) :
  2 * P_lower n - P_upper (n * n + n - 1) - ((n - 1 : ℝ) / (n * n : ℝ) - ((n - 1 : ℝ) / (n * n : ℝ))^2 / 2 + ((n - 1 : ℝ) / (n * n : ℝ))^3 / 3 - ((n - 1 : ℝ) / (n * n : ℝ))^4 / 4 + ((n - 1 : ℝ) / (n * n : ℝ))^5 / 5) ≤ x_seq n := by
  have h_eq := x_seq_eq n hn
  have h_E_lower := E_seq_lower n hn
  have hn2 : 2 ≤ n * n + n - 1 := by exact(2).le_pred_of_lt (Nat.add_le_add (n.mul_pos (by valid) (by valid)) (hn))
  have h_E_upper := E_seq_upper (n * n + n - 1) hn2
  have h_pos : 0 ≤ (n - 1 : ℝ) / (n * n : ℝ) := by linear_combination (by ·norm_cast: (1: ℝ)<n)/n^2
  have h_log := log_taylor_upper_5 ((n - 1 : ℝ) / (n * n : ℝ)) h_pos
  use h_eq▸ sub_le_sub (sub_le_sub (by ·bound) (h_E_upper.trans (by rw [ Nat.cast_pred (by valid),Nat.cast_add _, Nat.cast_mul]))) (h_log)

lemma x_seq_bounds_step2 (n : ℕ) (hn : 2 ≤ n) :
  x_seq n ≤ 2 * P_upper n - P_lower (n * n + n - 1) - ((n - 1 : ℝ) / (n * n : ℝ) - ((n - 1 : ℝ) / (n * n : ℝ))^2 / 2 + ((n - 1 : ℝ) / (n * n : ℝ))^3 / 3 - ((n - 1 : ℝ) / (n * n : ℝ))^4 / 4 + ((n - 1 : ℝ) / (n * n : ℝ))^5 / 5 - ((n - 1 : ℝ) / (n * n : ℝ))^6 / 6) := by
  have h_eq := x_seq_eq n hn
  have h_E_upper := E_seq_upper n hn
  have hn2 : 2 ≤ n * n + n - 1 := by match(n).le_mul_self with | S=>omega
  have h_E_lower := E_seq_lower (n * n + n - 1) hn2
  have h_pos : 0 ≤ (n - 1 : ℝ) / (n * n : ℝ) := by linear_combination (by norm_cast: (1: ℝ)<n)/n^2
  have h_log := log_taylor_lower_6 ((n - 1 : ℝ) / (n * n : ℝ)) h_pos
  use h_eq▸ sub_le_sub (sub_le_sub (by·bound) (h_E_lower.trans_eq' ↑(by rw [Nat.cast_pred (by·omega),Nat.cast_add _, Nat.cast_mul]))) (h_log)

lemma alg_bound1 (n : ℕ) (hn : 2 ≤ n) :
  5 / (6 * (n : ℝ)^2 + 6 * (n : ℝ)) < 2 * P_lower n - P_upper (n * n + n - 1) - ((n - 1 : ℝ) / (n * n : ℝ) - ((n - 1 : ℝ) / (n * n : ℝ))^2 / 2 + ((n - 1 : ℝ) / (n * n : ℝ))^3 / 3 - ((n - 1 : ℝ) / (n * n : ℝ))^4 / 4 + ((n - 1 : ℝ) / (n * n : ℝ))^5 / 5) := by delta P_lower P_upper
                                                                                                                                                                                                                                                                  field_simp[sub_eq_zero,(lt_add_of_pos_of_le _ _).ne',hn.trans']
                                                                                                                                                                                                                                                                  use(ge_of_eq (by rw [sub_div' ↑(pow_ne_zero 4 (by nlinarith only[pow_three (n : ℝ),show(n: ℝ) > 1by norm_cast])), mul_div,div_mul_eq_mul_div,div_mul_eq_mul_div, mul_sub, mul_div])).trans_lt' ?_
                                                                                                                                                                                                                                                                  rw[lt_sub_iff_add_lt',lt_div_iff₀' (pow_pos (by apply sub_pos.mpr (mod_cast one_lt_mul_of_lt_of_le hn n.succ_pos)) _),]
                                                                                                                                                                                                                                                                  nlinarith[ (by norm_cast: (2 :ℝ) ≤n),pow_three ((n-2)^2 : ℝ),pow_three ((n^2-4)^2 : ℝ),pow_three ((n^4-5)^2 : ℝ),mul_nonneg n.cast_nonneg (sq_nonneg ((n^6-8)^2: ℝ))]

lemma alg_bound2 (n : ℕ) (hn : 2 ≤ n) :
  2 * P_upper n - P_lower (n * n + n - 1) - ((n - 1 : ℝ) / (n * n : ℝ) - ((n - 1 : ℝ) / (n * n : ℝ))^2 / 2 + ((n - 1 : ℝ) / (n * n : ℝ))^3 / 3 - ((n - 1 : ℝ) / (n * n : ℝ))^4 / 4 + ((n - 1 : ℝ) / (n * n : ℝ))^5 / 5 - ((n - 1 : ℝ) / (n * n : ℝ))^6 / 6) ≤ 5 / (6 * (n : ℝ)^2 + 6 * (n : ℝ) - 1) := by norm_num[P_upper,P_lower,sub_add]
                                                                                                                                                                                                                                                                                                          field_simp[add_sub_assoc, two_mul,←mul_pow,←div_div]
                                                                                                                                                                                                                                                                                                          field_simp[show(n*6:ℝ)* (n + 1)-1≠0∧(n:ℝ) * (n + 1)-1≠00by repeat use by nlinarith only[show(n: ℝ) > 1by norm_cast]]
                                                                                                                                                                                                                                                                                                          rw[le_div_iff₀' (by bound[ (by norm_cast: (1: ℝ)<n)])]
                                                                                                                                                                                                                                                                                                          nlinarith[show(n: ℝ)≥2by simp_all,pow_three ((n-1)^2 : ℝ),pow_three ((n^2-1)^2 : ℝ),pow_three ((n^3-n)^2 : ℝ),mul_nonneg n.cast_nonneg<|sq_nonneg ((n^4-n^3: ℝ)^2)]

lemma K_bounds (n : ℕ) (hn : 1 ≤ n) :
  (6 * (n : ℝ)^2 + 6 * (n : ℝ) - 5) / 5 ≤ (((6 * n^2 + 6 * n - 1) / 5 : ℕ) : ℝ) ∧
  (((6 * n^2 + 6 * n - 1) / 5 : ℕ) : ℝ) ≤ (6 * (n : ℝ)^2 + 6 * (n : ℝ) - 1) / 5 := by exact (and_congr (div_le_iff₀ (by bound)) (le_div_iff₀ (by bound))).2 ((and_congr sub_le_iff_le_add le_sub_iff_add_le).2 (mod_cast (by valid)))

lemma bound1_step (n : ℕ) (hn : 2 ≤ n) : 1 / ((((6 * n^2 + 6 * n - 1) / 5 : ℕ) : ℝ) + (1 : ℝ)) ≤ 5 / (6 * (n : ℝ)^2 + 6 * (n : ℝ)) := by exact (div_le_div_iff₀ (Nat.cast_add_one_pos _) (by positivity)).2 ↑(mod_cast (by valid ) )

lemma bound2_step (n : ℕ) (hn : 2 ≤ n) : 5 / (6 * (n : ℝ)^2 + 6 * (n : ℝ) - 1) ≤ 1 / (((6 * n^2 + 6 * n - 1) / 5 : ℕ) : ℝ) := by exact (one_div_div _ _).ge.trans (one_div_le_one_div_of_le (mod_cast (by valid)) (Nat.cast_div_le.trans_eq ((congr_arg₂ _) ((Nat.cast_pred (by valid)).trans (by zify)) (rfl))))

lemma bound1 (n : ℕ) (hn : 2 ≤ n) :
  1 / ((((6 * n^2 + 6 * n - 1) / 5 : ℕ) : ℝ) + (1 : ℝ)) < x_seq n := by
  have h_step := x_seq_bounds_step n hn
  have h_alg := alg_bound1 n hn
  have h_K_bound := bound1_step n hn
  linarith

lemma bound2 (n : ℕ) (hn : 2 ≤ n) :
  x_seq n ≤ 1 / (((6 * n^2 + 6 * n - 1) / 5 : ℕ) : ℝ) := by
  have h_step := x_seq_bounds_step2 n hn
  have h_alg := alg_bound2 n hn
  have h_K_bound := bound2_step n hn
  linarith

lemma a_one : a 1 = 2 := by norm_num[a]
                            delta A227582_base
                            push_cast+decide[LinearRecurrence.mkSol]
lemma x_seq_one_bounds : 1 / 3 < x_seq 1 ∧ x_seq 1 ≤ 1 / 2 := by simp_rw [x_seq, one_div]
                                                                 use lt_sub_comm.1 (by_contra fun and=>absurd (@Real.tendsto_harmonic_sub_log) ? _),sub_le_comm.1 (by_contra fun and=>absurd (@Real.tendsto_harmonic_sub_log) ? _)
                                                                 · simp_all[harmonic_eq_sum_Icc, two_mul]
                                                                   use mt (le_of_tendsto · (@Filter.eventually_atTop.mpr ⟨9,Nat.le_induction le_rfl fun and I I' =>.trans (by_contra fun and' =>absurd ((.log and-Real.log (and + 1)).add_one_le_exp) ? _) I'⟩)) ?_
                                                                   · exact ( Finset.sum_Ico_eq_sum_range ↑(_ : ℕ → ℝ) _ _).symm▸by·linarith[ Real.lt_log_one_add_of_pos one_half_pos,Real.log_div three_ne_zero two_ne_zero, Real.log_two_gt_d9, @ Real.log_div @9 (3) (by(bound) ) three_ne_zero]
                                                                   · use and' ∘.trans (by rw [ Finset.sum_Icc_succ_top and.succ_pos, and.cast_succ]) ∘ (by linear_combination·.trans (by rw [Real.exp_sub,Real.exp_log (by positivity),Real.exp_log (by linarith)])+div_self_le_one (and+1:ℝ))
                                                                 · use and.comp (ge_of_tendsto · (Filter.eventually_atTop.2 ⟨9,fun R L=>match R with | S+1=>harmonic_succ S▸le_sub_iff_add_le.2 ?_⟩))
                                                                   refine(Rat.cast_le.2 ↑(le_add_of_nonneg_right (by positivity))).trans' ((8).le_induction (↑?_) ( fun and R M=>by_contra fun and' =>absurd ((.log (and+2)-Real.log (and + 1)).add_one_le_exp) ? _) S (by valid))
                                                                   · norm_num[harmonic,←le_sub_iff_add_le',Real.log_le_iff_le_exp _,((Real.sum_le_exp_of_nonneg _) 10).trans']
                                                                   push_cast[harmonic_succ,Real.exp_sub, (and+2:ℝ).exp_log (by positivity),Real.exp_log and.cast_add_one_pos]at*
                                                                   use and' ∘ (by·linear_combination(norm:=conv=>ring).+div_self_le_one (↑‹ℕ›+1 :ℝ)+M)

-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (n : ℕ) (hn : 0 < n) : a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) - (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat := by
  -- EVOLVE-BLOCK-START
  have h_val := a_val n hn
  by_cases h : 2 ≤ n
  · have h1 := bound1 n h
    have h2 := bound2 n h
    set K := (6 * n^2 + 6 * n - 1) / 5
    have h_a : a n = K := h_val
    have h_pos_K : (0 : ℝ) < (K : ℝ) := by exact (mod_cast(5).div_pos (by cases h with apply@le_add_self) (by decide) )
    have h_x_pos : 0 < x_seq n := by exact (.trans (by. (positivity ) ) h1)
    have h_K_plus_one_pos : (0 : ℝ) < (K : ℝ) + 1 := by linear_combination h_pos_K
    have h_lower : (K : ℝ) ≤ 1 / x_seq n := (le_one_div h_pos_K h_x_pos).mpr h2
    have h_upper : 1 / x_seq n < (K : ℝ) + 1 := (one_div_lt h_x_pos h_K_plus_one_pos).mpr h1
    have h_floor : Int.floor (1 / x_seq n) = (K : ℤ) := Int.floor_eq_iff.mpr ⟨h_lower, h_upper⟩
    have h_rewrite : 2 * (↑(harmonic n) : ℝ) - ↑(harmonic (n * n + n - 1)) - Real.eulerMascheroniConstant = x_seq n := rfl
    rw [h_rewrite]
    rw [h_floor]
    rw [h_a]
    exact (Int.toNat_natCast K).symm
  · have h_cases : n = 1 := by omega
    rcases h_cases with rfl
    have h_one : a 1 = 2 := a_one
    have h_bounds : 1 / 3 < x_seq 1 ∧ x_seq 1 ≤ 1 / 2 := x_seq_one_bounds
    have h_pos : 0 < x_seq 1 := by linarith
    have h_lower : (2 : ℝ) ≤ 1 / x_seq 1 := (le_one_div (by norm_num) h_pos).mpr h_bounds.2
    have h_upper : 1 / x_seq 1 < (2 : ℝ) + 1 := by norm_num only[*, one_div_lt h_pos]
    have h_floor : Int.floor (1 / x_seq 1) = 2 := Int.floor_eq_iff.mpr ⟨h_lower, h_upper⟩
    have h_rewrite : 2 * (↑(harmonic 1) : ℝ) - ↑(harmonic (1 * 1 + 1 - 1)) - Real.eulerMascheroniConstant = x_seq 1 := rfl
    rw [h_rewrite, h_floor, h_one]
    exact rfl
  -- EVOLVE-BLOCK-END
