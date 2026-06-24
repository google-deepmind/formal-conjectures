/-
Copyright 2025 Google LLC

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

/-
Copyright 2025 Google LLC

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


open Finset Nat Real Filter Asymptotics

/--
A051293: Number of nonempty subsets of $\{1, 2, 3, \dots, n\}$ whose elements have an integer average.
-/
def A051293 (n : ℕ) : ℕ :=
  Finset.card (
    (Finset.Icc 1 n).powerset.filter fun S : Finset ℕ =>
      S.Nonempty ∧ S.card ∣ S.sum id
  )

noncomputable def a_real (n : ℕ) : ℝ := A051293 n

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
noncomputable def I_sum (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k * (Nat.choose n k : ℝ)

noncomputable def S_sum (n : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 n, (2 : ℝ)^j / (j : ℝ)

noncomputable def H_sum (n : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 n, (1 : ℝ) / (j : ℝ)

lemma I_sum_eq (n : ℕ) : I_sum n = S_sum n - H_sum n := by
  delta S_sum I_sum and H_sum
  refine n.rec ((sub_self _)).symm fun and x =>(((( Finset.sum_Icc_succ_top and.succ_pos _)).trans) ? _).trans (by rw [ Finset.sum_Icc_succ_top and.succ_pos, Finset.sum_Icc_succ_top and.succ_pos,add_sub_add_comm,<-x])
  refine mod_cast (and+1).sum_range_choose▸.trans (by rw [ Finset.sum_congr rfl fun and μ=>by rw [Nat.choose_succ_left _ _ (Finset.mem_Icc.1 μ).1,Nat.cast_add, mul_add], Finset.sum_add_distrib, add_assoc]) ?_
  norm_num[add_comm 1,inv_mul_eq_div, add_left_comm, add_div, Finset.sum_range_succ' _ (and+1), Finset.sum_range_succ,Finset.sum_div]at*
  refine(Finset.sum_Ico_eq_sum_range _ _ _).trans ((congr_arg _) ((funext (add_comm · (1)▸(div_eq_div_iff (by norm_cast) (by norm_cast)).2 (mod_cast and.succ_mul_choose_eq _▸mul_comm _ _)))))

def M0 : ℝ := 2
def P0 (n : ℝ) : ℝ := 1

def M1 : ℝ := 2
def P1 (n : ℝ) : ℝ := n + 1

def M2 : ℝ := 6
def P2 (n : ℝ) : ℝ := n^2 + 2*n + 3

def M3 : ℝ := 26
def P3 (n : ℝ) : ℝ := n^3 + 3*n^2 + 9*n + 13

def M4 : ℝ := 150
def P4 (n : ℝ) : ℝ := n^4 + 4*n^3 + 18*n^2 + 52*n + 75

def M5 : ℝ := 1082
def P5 (n : ℝ) : ℝ := n^5 + 5*n^4 + 30*n^3 + 130*n^2 + 375*n + 541

lemma s0_eq (n : ℕ) : ∑ k ∈ Finset.range n, (1 : ℝ) / 2^k = M0 - P0 n * 2 / 2^n := by norm_num only [geom_sum_eq, M0,←one_div_pow, P0]
                                                                                      exact (.trans (by rw [ one_div_pow]) (by(ring)))
lemma s1_eq (n : ℕ) : ∑ k ∈ Finset.range n, (k : ℝ) / 2^k = M1 - P1 n * 2 / 2^n := by push_cast only[←inv_pow, M1,div_eq_mul_inv, P1]
                                                                                      induction n with|zero =>ring |succ R L=>exact ( Finset.sum_range_succ _ _).trans (.symm (L▸.trans (by rw [ R.cast_succ]) (by·ring)))
lemma s2_eq (n : ℕ) : ∑ k ∈ Finset.range n, (k : ℝ)^2 / 2^k = M2 - P2 n * 2 / 2^n := by delta P2
                                                                                        exact (symm (.trans (by rw [M2]) (by induction n with|zero=>ring |succ R L=>exact (.trans (by rw [ R.cast_succ]) (( Finset.sum_range_succ _ _).trans (by exact L▸by·ring1)).symm))))
lemma s3_eq (n : ℕ) : ∑ k ∈ Finset.range n, (k : ℝ)^3 / 2^k = M3 - P3 n * 2 / 2^n := by rw[P3, M3,@ Finset.sum_range_induction]
                                                                                        · norm_num
                                                                                        · use fun and n=>.trans (by rw [Nat.cast_succ]) (by ring!)
lemma s4_eq (n : ℕ) : ∑ k ∈ Finset.range n, (k : ℝ)^4 / 2^k = M4 - P4 n * 2 / 2^n := by delta M4 P4
                                                                                        symm
                                                                                        induction n with|zero=>ring|_ A B=>exact (.trans (B▸.trans (by rw [ A.cast_succ]) (by ring)) ( Finset.sum_range_succ _ _).symm)
lemma s5_eq (n : ℕ) : ∑ k ∈ Finset.range n, (k : ℝ)^5 / 2^k = M5 - P5 n * 2 / 2^n := by push_cast only [div_eq_mul_inv, P5,←inv_pow]
                                                                                        induction n with|zero=>norm_num[ M5]|_ A B=>exact ( Finset.sum_range_succ _ _).trans (symm (B▸.trans (by rw [ A.cast_succ]) (by ring)))

lemma frac_identity (n k : ℕ) (h1 : k < n) : (1 : ℝ) / (n - k) = 1 / n + k / n^2 + k^2 / n^3 + k^3 / n^4 + k^4 / n^5 + k^5 / n^6 + k^6 / (n^6 * (n - k)) := by field_simp [hzero /mul_zero, sub_eq_zero]
                                                                                                                                                               exact (eq_div_of_mul_eq fun and=>by simp_all ((add_div' _ _ _ fun and=>by simp_all[sub_eq_zero]).trans (by ring)).symm)

lemma S_sum_expansion (n : ℕ) (h : 0 < n) : S_sum n =
    (2^n / n) * (∑ k ∈ Finset.range n, (1 : ℝ) / 2^k) +
    (2^n / n^2) * (∑ k ∈ Finset.range n, (k : ℝ) / 2^k) +
    (2^n / n^3) * (∑ k ∈ Finset.range n, (k : ℝ)^2 / 2^k) +
    (2^n / n^4) * (∑ k ∈ Finset.range n, (k : ℝ)^3 / 2^k) +
    (2^n / n^5) * (∑ k ∈ Finset.range n, (k : ℝ)^4 / 2^k) +
    (2^n / n^6) * (∑ k ∈ Finset.range n, (k : ℝ)^5 / 2^k) +
    ∑ k ∈ Finset.range n, (2^(n - k) * (k : ℝ)^6) / (n^6 * (n - k)) := by push_cast only[mul_one_div, true, ← Finset.sum_add_distrib, S_sum, mul_div_mul_comm, true, Finset.mul_sum]
                                                                          refine(Finset.sum_Ico_eq_sub ↑_ (n : ℕ).succ_pos).trans (n.rec ↑(sub_self _) fun and x =>((( Finset.sum_range_succ' _ _).trans) ? _).symm)
                                                                          refine if a : and=0 then a.symm▸by {norm_num} else(((congr_arg₂ _).comp ( Finset.sum_congr rfl fun and x =>?_).trans x.symm (by ring))).trans (.trans (add_sub_right_comm _ _ _).symm ((congr_arg₂ _) (Finset.sum_range_succ _ _).symm rfl))
                                                                          field_simp[←add_div _,←div_div, sub_eq_zero,(List.mem_range.1 x).ne',Nat.add_sub_add_right]
                                                                          push_cast[mul_assoc,eq_self,←pow_add,mul_left_comm (2^and : ℝ),add_sub_add_right_eq_sub, and.add_sub_of_le (List.mem_range.1 x).le]
                                                                          exact (Nat.succ_eq_add_one @_).symm▸by match and.add_sub_of_le (@List.mem_range.1 x).le▸pow_add (@2 : ℝ) _ _ with | S=>grind

noncomputable def E_poly (n : ℝ) : ℝ :=
  2 * P0 n / n + 2 * P1 n / n^2 + 2 * P2 n / n^3 + 2 * P3 n / n^4 + 2 * P4 n / n^5 + 2 * P5 n / n^6

lemma tendsto_pow_div_exp (k : ℕ) : Tendsto (fun n : ℕ => ((n:ℝ)^k) / (2:ℝ)^n) atTop (nhds 0) := by
  exact tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)

lemma E_poly_limit : Tendsto (fun n : ℕ => E_poly n / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))) atTop (nhds 0) := by
  simp_rw [div_div_eq_mul_div,E_poly]
  delta P2 P3 P5 and P0 P1 P4
  classical ring
  repeat apply add_zero (@0: ℝ)▸Filter.Tendsto.add
  · exact (tendsto_pow_const_mul_const_pow_of_lt_one 5 one_half_pos.le (by norm_num)).congr (by cases · with field_simp [pow_succ])
  · exact (tendsto_pow_const_mul_const_pow_of_lt_one ↑4 (by((((norm_num))))) (by ·norm_num)).congr fun and=>congr_arg (@·* _) (by((field_simp)))
  · use(((tendsto_pow_const_mul_const_pow_of_abs_lt_one (3) (by bound)).congr fun and=>congr_arg (.* _) (by field_simp[←pow_add])).mul_const _).trans (by rw [zero_mul])
  · exact(((tendsto_pow_const_mul_const_pow_of_lt_one (2) one_half_pos.le (by norm_num)).congr' ((Filter.eventually_ne_atTop 0).mono fun and x =>by field_simp[←pow_add])).mul_const _).trans (by simp_all)
  · use(((tendsto_self_mul_const_pow_of_lt_one one_half_pos.le (by norm_num)).congr' ((Filter.eventually_ne_atTop 0).mono fun and y=>by field_simp[←pow_succ])).mul_const _).trans (by rw [zero_mul])
  · exact(((summable_geometric_two).congr_atTop.comp (Filter.eventually_ne_atTop @0).mono ↑(by simp_all)).mul_right @541).tendsto_atTop_zero
  · use((tendsto_pow_const_mul_const_pow_of_lt_one 5 one_half_pos.le (by bound)).congr (by cases em<|.=0 with norm_num[*,←zpow_neg,←zpow_natCast,←zpow_add']))
  · refine(((tendsto_pow_const_mul_const_pow_of_lt_one 4 one_half_pos.le one_half_lt_one).congr' ((Filter.eventually_ne_atTop 0).mono fun and x =>by field_simp [←pow_add])).mul_const _).trans (by rw [zero_mul])
  · use(((tendsto_pow_const_mul_const_pow_of_lt_one 3 one_half_pos.le one_half_lt_one).congr'<|Filter.eventually_atTop.2 ⟨1,fun _ _=>by field_simp[←pow_add]⟩).mul_const _).trans (by rw [zero_mul])
  · use(((tendsto_pow_const_mul_const_pow_of_lt_one (2) one_half_pos.le one_half_lt_one).congr' ((Filter.eventually_ne_atTop 0).mono fun and j=>by field_simp[←pow_add])).mul_const _).trans (by rw [zero_mul])
  · use(((tendsto_pow_const_mul_const_pow_of_lt_one (1) one_half_pos.le (by norm_num)).congr' ((Filter.eventually_ne_atTop 0).mono<|by simp_all[←zpow_neg,←zpow_natCast,←zpow_add'])).mul_const _).trans (by rw [zero_mul])
  · use((tendsto_pow_const_mul_const_pow_of_lt_one 05 one_half_pos.le (by·norm_num)).congr (by if a : ·=0 then{bound} else {field_simp[←pow_add] }) )
  · use(((tendsto_pow_const_mul_const_pow_of_lt_one 4 one_half_pos.le (by bound)).congr' ((Filter.eventually_ne_atTop 0).mono fun and y=>by field_simp[←pow_add])).mul_const _).trans (by simp_all)
  · use(((tendsto_pow_const_mul_const_pow_of_lt_one (3) one_half_pos.le one_half_lt_one).congr' ((Filter.eventually_ne_atTop 0).mono fun and y=>by field_simp[←pow_add])).mul_const _).trans (by rw [zero_mul])
  · apply(((tendsto_pow_const_mul_const_pow_of_lt_one (2) one_half_pos.le one_half_lt_one).congr' ((Filter.eventually_ne_atTop ↑0).mono fun and x =>by field_simp [←pow_add])).mul_const _).trans (by rw [zero_mul])
  · use((tendsto_pow_const_mul_const_pow_of_lt_one 5 one_half_pos.le one_half_lt_one).congr' ((Filter.eventually_ne_atTop 0).mono fun and y=>by field_simp[←pow_add]))
  · use(((tendsto_pow_const_mul_const_pow_of_lt_one 4 one_half_pos.le one_half_lt_one).congr' ((Filter.eventually_ne_atTop 0).mono fun and y=>by field_simp[←pow_add])).mul_const _).trans (by rw [zero_mul])
  · use(((tendsto_pow_const_mul_const_pow_of_lt_one (3) one_half_pos.le (by norm_num)).congr' ((Filter.eventually_ne_atTop 0).mono fun and y=>by field_simp[←pow_add])).mul_const _).trans (by rw [zero_mul])
  · use((tendsto_pow_const_mul_const_pow_of_lt_one 5 one_half_pos.le one_half_lt_one)).congr fun and=>by linear_combination-div_self_mul_self (and^5: ℝ)*2⁻¹^and
  · use(((tendsto_pow_const_mul_const_pow_of_lt_one 4 one_half_pos.le (by norm_num)).congr' ((Filter.eventually_ne_atTop 0).mono (by field_simp[←pow_add,.|>.succ_pos,.]))).mul_const _).trans (by rw [zero_mul])
  · exact (tendsto_pow_const_mul_const_pow_of_lt_one 5 (by norm_num) (by norm_num)).congr fun and=>congr_arg (.* _) (by if a:and=0 then{bound} else field_simp[←pow_add])

lemma R_n_limit : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, (k : ℝ)^6 / (2^(k+1) * (n - k))) atTop (nhds 0) := by have := (summable_pow_mul_geometric_of_norm_lt_one 06 ↑(Real.norm_of_nonneg one_half_pos.le▸one_half_lt_one)).mul_left (1: ℝ)
                                                                                                                    replace: (Filter.Tendsto fun and : ℕ =>∑' (n : ℕ),ite (n<and) (n^6/ (2 ^ (n + 1)*(and -n)) : ℝ) 0) ↑.atTop (𝓝 0)
                                                                                                                    · use(tendsto_tsum_of_dominated_convergence this ( fun and=>?_) (.of_forall fun and=>?_)).trans (by rw [tsum_zero])
                                                                                                                      · apply(((tendsto_natCast_atTop_atTop.atTop_add ↑tendsto_const_nhds).const_mul_atTop (by positivity)).const_div_atTop (@_)).if' ↑tendsto_const_nhds
                                                                                                                      use fun and' =>or_not.elim (if_pos ·▸.trans (abs_of_nonneg (by bound[ (by gcongr: (and: ℝ)>and')])).le ? _) (if_neg ·▸mod_cast (by positivity))
                                                                                                                      norm_num[div_eq_mul_inv, sub_eq_neg_add,←inv_pow,mul_assoc,le_mul_of_one_le_right _, (by norm_cast: (and: ℝ)≥and'+1),pow_add]
                                                                                                                      exact (mul_le_mul_of_nonneg_left ((mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ (mod_cast (by valid)))).trans (mul_le_of_le_one_left (by positivity) (by norm_num))) (by bound))
                                                                                                                    · simp_all only [ ← Finset.mem_range, if_pos,tsum_eq_sum fun and β=>if_neg β]

lemma S_sum_diff_eq (n : ℕ) (h : 0 < n) :
  (S_sum n - ((2 : ℝ) ^ (n + 1) / (n : ℝ)) * ((1 : ℝ) + 1 / (n : ℝ) + 3 / ((n : ℝ) ^ 2) + 13 / ((n : ℝ) ^ 3) + 75 / ((n : ℝ) ^ 4) + 541 / ((n : ℝ) ^ 5))) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6)) =
  (∑ k ∈ Finset.range n, (k : ℝ)^6 / (2^(k+1) * (n - k))) - E_poly n / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6)) := by
  have h_exp := S_sum_expansion n h
  have h0 := s0_eq n
  have h1 := s1_eq n
  have h2 := s2_eq n
  have h3 := s3_eq n
  have h4 := s4_eq n
  have h5 := s5_eq n
  have h_sum_eq : ∑ k ∈ Finset.range n, 2 ^ (n - k) * (k : ℝ) ^ 6 / (↑n ^ 6 * (↑n - ↑k)) =
    (2 : ℝ)^(n+1) / (n:ℝ)^6 * ∑ k ∈ Finset.range n, (k : ℝ)^6 / (2^(k+1) * (n - k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk_lt : k < n := Finset.mem_range.mp hk
    have h2 : (2:ℝ)^(k+1) ≠ 0 := by positivity
    have h_pow_eq : (2:ℝ)^(n-k) * (2:ℝ)^(k+1) = (2:ℝ)^(n+1) := by
      rw [← pow_add]
      congr 1
      omega
    have h_eq : (2:ℝ)^(n-k) = (2:ℝ)^(n+1) / (2:ℝ)^(k+1) := by
      rw [← h_pow_eq]
      exact (mul_div_cancel_right₀ _ h2).symm
    rw [h_eq]
    have h_ring : ((2:ℝ)^(n+1) / (2:ℝ)^(k+1)) * (k:ℝ)^6 / ((n:ℝ)^6 * ((n:ℝ) - k)) = ((2:ℝ)^(n+1) / (n:ℝ)^6) * ((k:ℝ)^6 / ((2:ℝ)^(k+1) * ((n:ℝ) - k))) := by
      generalize (2:ℝ)^(n+1) = A
      generalize (2:ℝ)^(k+1) = B
      generalize (k:ℝ)^6 = C
      generalize (n:ℝ)^6 = D
      generalize ((n:ℝ) - k) = E
      ring
    exact h_ring
  have h_S_eq : S_sum n = ((2 : ℝ) ^ (n + 1) / (n : ℝ)) * ((1 : ℝ) + 1 / (n : ℝ) + 3 / ((n : ℝ) ^ 2) + 13 / ((n : ℝ) ^ 3) + 75 / ((n : ℝ) ^ 4) + 541 / ((n : ℝ) ^ 5)) - E_poly n + ((2 : ℝ)^(n+1) / (n:ℝ)^6) * ∑ k ∈ Finset.range n, (k : ℝ)^6 / (2^(k+1) * (n - k)) := by
    rw [h_exp, h0, h1, h2, h3, h4, h5, h_sum_eq]
    unfold M0 M1 M2 M3 M4 M5 E_poly P0 P1 P2 P3 P4 P5
    have h2n : (2:ℝ)^(n+1) = (2:ℝ)^n * 2 := by rw [pow_add, pow_one]
    rw [h2n]
    have hn : (n:ℝ) ≠ 0 := by positivity
    have h2n_neq : (2:ℝ)^n ≠ 0 := by positivity
    field_simp
    ring
  rw [h_S_eq]
  have h_denom : ((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6) ≠ 0 := by positivity
  have h_div : ∀ (A M E D R : ℝ), D ≠ 0 → (M - E + D * R - M) / D = R - E / D := by
    intro A M E D R hD
    calc (M - E + D * R - M) / D = (D * R - E) / D := by ring
      _ = D * R / D - E / D := by ring
      _ = R - E / D := by rw [mul_div_cancel_left₀ R hD]
  exact h_div (S_sum n) _ (E_poly n) _ _ h_denom

lemma S_sum_asymp : Tendsto (fun n : ℕ => (S_sum n - ((2 : ℝ) ^ (n + 1) / (n : ℝ)) * ((1 : ℝ) + 1 / (n : ℝ) + 3 / ((n : ℝ) ^ 2) + 13 / ((n : ℝ) ^ 3) + 75 / ((n : ℝ) ^ 4) + 541 / ((n : ℝ) ^ 5))) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))) atTop (nhds 0) := by
  have h1 := R_n_limit
  have h2 := E_poly_limit
  have h3 : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, (k : ℝ)^6 / (2^(k+1) * (n - k))) - E_poly n / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))) atTop (nhds (0 - 0)) := Tendsto.sub h1 h2
  rw [sub_zero] at h3
  have h4 : (fun n : ℕ => (S_sum n - ((2 : ℝ) ^ (n + 1) / (n : ℝ)) * ((1 : ℝ) + 1 / (n : ℝ) + 3 / ((n : ℝ) ^ 2) + 13 / ((n : ℝ) ^ 3) + 75 / ((n : ℝ) ^ 4) + 541 / ((n : ℝ) ^ 5))) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))) =ᶠ[atTop] (fun n : ℕ => (∑ k ∈ Finset.range n, (k : ℝ)^6 / (2^(k+1) * (n - k))) - E_poly n / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    exact S_sum_diff_eq n hn
  exact Tendsto.congr' h4.symm h3

lemma H_sum_asymp : Tendsto (fun n : ℕ => H_sum n / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))) atTop (nhds 0) := by
  push_cast only[pow_succ, H_sum, true,div_div_eq_mul_div]
  apply squeeze_zero fun and=>by positivity fun and=>div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (Finset.sum_le_card_nsmul _ _ _ fun and=>div_le_self one_pos.le ∘by simp_all) (by bound)) (by bound)
  use(((tendsto_pow_const_div_const_pow_of_one_lt 7 one_lt_two).div_const 2).congr fun and=>Nat.card_Icc _ _▸by ring!).trans (by rw [zero_div])

lemma I_asymp : Tendsto (fun n : ℕ => (I_sum n - ((2 : ℝ) ^ (n + 1) / (n : ℝ)) * ((1 : ℝ) + 1 / (n : ℝ) + 3 / ((n : ℝ) ^ 2) + 13 / ((n : ℝ) ^ 3) + 75 / ((n : ℝ) ^ 4) + 541 / ((n : ℝ) ^ 5))) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))) atTop (nhds 0) := by
  have h1 := S_sum_asymp
  have h2 := H_sum_asymp
  have h3 : Tendsto (fun n : ℕ => (S_sum n - ((2 : ℝ) ^ (n + 1) / (n : ℝ)) * ((1 : ℝ) + 1 / (n : ℝ) + 3 / ((n : ℝ) ^ 2) + 13 / ((n : ℝ) ^ 3) + 75 / ((n : ℝ) ^ 4) + 541 / ((n : ℝ) ^ 5))) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6)) - H_sum n / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))) atTop (nhds (0 - 0)) := Tendsto.sub h1 h2
  have h4 : (fun n : ℕ => (S_sum n - ((2 : ℝ) ^ (n + 1) / (n : ℝ)) * ((1 : ℝ) + 1 / (n : ℝ) + 3 / ((n : ℝ) ^ 2) + 13 / ((n : ℝ) ^ 3) + 75 / ((n : ℝ) ^ 4) + 541 / ((n : ℝ) ^ 5))) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6)) - H_sum n / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))) = (fun n : ℕ => (I_sum n - ((2 : ℝ) ^ (n + 1) / (n : ℝ)) * ((1 : ℝ) + 1 / (n : ℝ) + 3 / ((n : ℝ) ^ 2) + 13 / ((n : ℝ) ^ 3) + 75 / ((n : ℝ) ^ 4) + 541 / ((n : ℝ) ^ 5))) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))) := by
    ext n
    rw [I_sum_eq]
    ring
  rw [sub_zero] at h3
  rw [h4] at h3
  exact h3

noncomputable def S_real (n k : ℕ) : ℝ :=
  (Finset.card ((Finset.Icc 1 n).powerset.filter fun S => S.card = k ∧ k ∣ S.sum id) : ℝ)

lemma a_real_eq_sum_S_real (n : ℕ) : a_real n = ∑ k ∈ Finset.Icc 1 n, S_real n k := by
  delta and S_real a_real
  push_cast[ Finset.card_filter, A051293, false,id]
  exact ( Finset.sum_comm.trans ( Finset.sum_congr rfl fun and β=>by norm_num[ (and.card_mono (Finset.mem_powerset.1 β)).trans,ite_and,Nat.succ_sub_one _,Nat.succ_le])).symm

/--
`S_real n k` is the number of $k$-element subsets of $\{1, 2, \dots, n\}$ whose sum is divisible by $k$.
By the roots of unity filter, this exact count can be written as:
$S_{n,k} = \frac{1}{k} \sum_{j=0}^{k-1} \sum_{A \in \binom{n}{k}} \omega^{j \sum A}$.
The main term $j=0$ yields exactly $\frac{1}{k} \binom{n}{k}$.
For $j > 0$, the roots of unity evaluated over the subsets yield bounded periodic sums.
The maximal magnitude of these periodic products is achieved when the order of the root is 2,
which bounds the error term magnitude strictly by $2 \cdot 2^{n/2}$.
-/
noncomputable def P_poly (n : ℕ) (ω : ℂ) : Polynomial ℂ :=
  ∏ x ∈ Finset.Icc 1 n, (1 + C (ω^x) * X)

lemma coeff_P_poly (n k : ℕ) (ω : ℂ) :
  (P_poly n ω).coeff k = ∑ S ∈ (Finset.Icc 1 n).powerset.filter (fun S => S.card = k), ω ^ (S.sum id) := by
  norm_num[T_ /em, P_poly]
  norm_num[add_comm (1 : ℂ[X]), Finset.prod_add, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum _,← Finset.powersetCard_eq_filter]
  norm_num [←map_pow, false, Finset.powersetCard_eq_filter, Eq.comm, Finset.sum_filter]

noncomputable def sum_abs_coeff (P : Polynomial ℂ) : ℝ :=
  ∑ i ∈ P.support, ‖P.coeff i‖

lemma coeff_le_sum_abs (P : Polynomial ℂ) (k : ℕ) :
  ‖P.coeff k‖ ≤ sum_abs_coeff P := by
  delta sum_abs_coeff
  exact (em _).elim ↑(norm_eq_zero.2 · |>.trans_le (by ·positivity)) ( Finset.single_le_sum (fun a s=>norm_nonneg _) ∘mem_support_iff.mpr)

lemma sum_abs_coeff_mul (P Q : Polynomial ℂ) :
  sum_abs_coeff (P * Q) ≤ sum_abs_coeff P * sum_abs_coeff Q := by
  push_cast [coeff_mul,sum_abs_coeff, true, Finset.sum_mul_sum]
  trans∑ a ∈(P*Q).support,∑M ∈P.support ×ˢQ.support,ite (M.1+M.2 = a) (norm (P.coeff M.1) *norm (Q.coeff M.2)) 0
  · exact Finset.sum_le_sum fun and x =>(norm_sum_le_of_le @_ fun and β=>norm_mul_le _ _).trans (.trans ( Finset.sum_subset fun and=>by simp_all (by cases em<|P.coeff ·.1=0 with simp_all)).ge (Finset.sum_filter _ _).le)
  · use Finset.sum_comm.trans_le (( Finset.sum_product _ _ _).trans_le (Finset.sum_le_sum fun and n=> Finset.sum_le_sum (by cases em<|and+. ∈(P*Q).support with norm_num[mul_nonneg _, *])))

lemma sum_abs_coeff_pow (P : Polynomial ℂ) (m : ℕ) :
  sum_abs_coeff (P ^ m) ≤ (sum_abs_coeff P) ^ m := by
  delta sum_abs_coeff
  use(Finset.sum_le_sum_of_subset_of_nonneg supp_subset_range_natDegree_succ (by bound)).trans (m.rec (by simp_all[coeff_one]) fun and J=>.trans (by rw [ Finset.sum_congr rfl fun and n=>by rw [pow_succ,coeff_mul]]) ? _)
  simp_all[ Finset.mul_sum, add_mul, Finset.Nat.antidiagonal_eq_map, P.support.sum_subset supp_subset_range_natDegree_succ,pow_add]
  trans∑ a ∈.range (and* P.natDegree+natDegree P+1),∑M ∈.range (and* P.natDegree+1),ite (M ≤ a) (norm ((P^and).coeff M)*norm (P.coeff (a-M))) 0
  · refine if a: P=0 then (by ·norm_num[a])else ((congr_arg₂ _) (by (norm_num[a,natDegree_mul])) ↑(rfl)).le.trans ( Finset.sum_le_sum fun and x =>(norm_sum_le _ _).trans (?_) )
    exact ( Finset.sum_subset fun and=>by simp_all[and.lt_succ] (by simp_all[coeff_eq_zero_of_natDegree_lt,·.lt_succ])).ge.trans_eq ((congr_arg _ (by simp_rw [norm_mul])).trans ( Finset.sum_filter _ _))
  refine Finset.sum_comm.trans_le.comp ( Finset.sum_le_sum fun and Z=>? _).trans ( Finset.sum_comm.trans_le (Finset.sum_le_sum fun and x =>( Finset.sum_mul _ _ _).ge.trans (mul_le_mul_of_nonneg_right J (by bound))))
  norm_num[←Nat.Ico_zero_eq_range, Finset.sum_ite]
  exact ( Finset.sum_Ico_eq_sum_range _ _ _).trans_le (Finset.range_eq_Ico▸ ((congr_arg _) (by simp_rw [and.add_sub_cancel_left])).trans_le (Finset.sum_subset ↑(List.range_subset.mpr (by·grind)) (by simp_all [coeff_eq_zero_of_natDegree_lt, true,Nat.succ_le])).ge)

lemma sum_abs_coeff_one_add_C_X (ω : ℂ) (hω : ‖ω‖ = 1) :
  sum_abs_coeff (1 + C ω * X) = 2 := by
  norm_num[sum_abs_coeff]
  norm_num[*,coeff_one,coeff_X,( Finset.ext (by match. with|0|1 | S+2=>simp_all[coeff_one,coeff_X,←norm_ne_zero_iff]):(1+C ω*X).support={0,1})]

lemma sum_abs_coeff_one_sub_X_pow (d : ℕ) (hd : 0 < d) :
  sum_abs_coeff (1 - (-X)^d) = 2 := by
  norm_num [sum_abs_coeff, Polynomial.coeff_one, sub_eq_add_neg]
  cases d.even_or_odd with norm_num+contextual[*, Odd.neg_pow, Polynomial.coeff_one,hd.ne,hd.ne',eq_comm, Finset.sum_eq_add_sum_diff_singleton (show 0 ∈_ from _), Finset.sum_eq_single d]

lemma P_poly_split (n d : ℕ) (hd : 0 < d) (ω : ℂ) (hω : IsPrimitiveRoot ω d) :
  P_poly n ω = (1 - (-X)^d) ^ (n / d) * ∏ x ∈ Finset.Ico (n / d * d + 1) (n + 1), (1 + C (ω^x) * X) := by
  delta P_poly Real
  let B: Polynomial ℂ:=1-.X^d
  refine(Finset.prod_Ico_consecutive _ (by push_cast) (by push_cast[n.div_mul_le_self])).symm.trans (congr_arg (.* _) (( Finset.prod_Ico_eq_prod_range _ _ _).trans ((n/d).rec (d.mul_comm 0▸rfl) ?_)))
  simp_all[pow_add, sub_eq_add_neg, add_mul,pow_mul',IsPrimitiveRoot.iff_def,Finset.prod_range_add]
  replace:X^d-1=∏ a ∈.range d,(X-C (ω^ a)) := (eq_of_degree_sub_lt_of_eval_finset_eq (.image (ω^·) (.range d)) ?_) ?_
  · use fun and x =>.inl (funext fun and=>by_contra fun and' =>absurd (congr_arg (eval (-1/(ω*and))) this).symm (and' ∘?_))
    obtain ⟨@c⟩ :=eq_or_ne and 0
    · norm_num[hd.ne']
      norm_num[eval_prod]
    · norm_num[eval_prod, sub_eq_add_neg, mul_pow,mul_right_comm,div_pow,div_add',pow_ne_zero_iff hd.ne'|>.1 (hω.1▸one_ne_zero),hω,by valid]
      exact ( Finset.prod_congr rfl fun and x =>by ring).trans.comp ( Finset.prod_mul_distrib.trans.comp (congr_arg₂ _ · (Finset.prod_const (-1)) |>.trans (by cases d.even_or_odd with norm_num[add_comm, Odd.neg_pow, *])))
  · convert degree_sub_lt .. using 0x1
    · erw[degree_X_pow_sub_C hd, Finset.card_image_of_injOn ((IsPrimitiveRoot.mk_of_lt ω hd hω.1 fun and A B=>by valid ∘d.eq_zero_of_dvd_of_lt ∘hω.2 and).injOn_pow), Finset.card_range]
    · exact (degree_X_pow_sub_C hd _).trans ( (by·simp_rw [degree_prod,degree_X_sub_C, Finset.sum_const,nsmul_one _, Finset.card_range]))
    · apply X_pow_sub_C_ne_zero hd
    · norm_num[leadingCoeff_prod,hd,<-map_pow]
  · use Finset.forall_mem_image.2 fun and β=>by norm_num[eval_prod, C_pow,pow_right_comm, Finset.prod_eq_zero β, *]

lemma sum_abs_coeff_prod_Ico (a b : ℕ) (ω : ℂ) (hω : ‖ω‖ = 1) :
  sum_abs_coeff (∏ x ∈ Finset.Ico a b, (1 + C (ω^x) * X)) ≤ (2 : ℝ) ^ (b - a) := by
  norm_num[add_comm (1 : ℂ[X]),sum_abs_coeff,←map_pow, Finset.prod_add]
  use(Finset.sum_le_sum fun and Y=>norm_sum_le _ _).trans ( Finset.sum_comm.trans_le (( Finset.sum_le_sum fun and Z=>? _).trans (by rw [ Finset.sum_const,nsmul_one, Finset.card_powerset, a.card_Ico,Nat.cast_pow,Nat.cast_two])))
  norm_num[*, and.prod_mul_distrib,←map_pow,←map_prod]
  exact (em _).elim (by simp_all[ Finset.sum_eq_single_of_mem and.card]) (Finset.sum_eq_zero.comp ( fun and A B=>norm_eq_zero.2 (if_neg (and.comp (.▸B)))) ·|>.trans_le (by bound))

lemma P_poly_bound (n : ℕ) (ω : ℂ) (d : ℕ) (hd : 0 < d) (hω : IsPrimitiveRoot ω d) (hω_norm : ‖ω‖ = 1) :
  sum_abs_coeff (P_poly n ω) ≤ (2 : ℝ) ^ (n / d + n % d) := by
  have h_split := P_poly_split n d hd ω hω
  rw [h_split]
  have h_mul := sum_abs_coeff_mul ((1 - (-X)^d) ^ (n / d)) (∏ x ∈ Finset.Ico (n / d * d + 1) (n + 1), (1 + C (ω^x) * X))
  have h_left : sum_abs_coeff ((1 - (-X)^d) ^ (n / d)) ≤ (2 : ℝ) ^ (n / d) := by
    norm_num[<-pow_mul,sum_abs_coeff,sub_eq_neg_add,add_pow]
    use(Finset.sum_le_sum fun and x =>norm_sum_le _ _).trans ( Finset.sum_comm.trans_le (mod_cast(n/d).sum_range_choose▸?_))
    use(Finset.sum_le_sum fun A B=>.trans ( Finset.sum_le_sum fun and n=>norm_mul_le_of_le (show _≤ ite (and = d*A) (1) 0 from(?_)) (by rw [])) @? _).trans (by rw [Nat.cast_sum])
    · cases A.even_or_odd with cases em (and = d*A) with cases d.even_or_odd with norm_num[*, Odd.neg_pow,<-pow_mul]
    · exact (em _).elim (Finset.sum_eq_single_of_mem _ · ( fun and R L=>by rw [if_neg L,zero_mul])|>.trans_le (by norm_num)) ( Finset.sum_eq_zero.comp ( fun and R L=>by rw [if_neg (by bound),zero_mul]) ·|>.trans_le (by bound))
  have h_right : sum_abs_coeff (∏ x ∈ Finset.Ico (n / d * d + 1) (n + 1), (1 + C (ω^x) * X)) ≤ (2 : ℝ) ^ (n % d) := by
    norm_num [add_comm (1 : ℂ[X]),sum_abs_coeff,←map_pow,n.mod_def]
    trans∑b ∈.range (n-n/d*d+1),norm ((∏ a ∈.Ico (n/d*d+1) (n + 1),(C (ω^a)*X + 1)).coeff b)
    · exact Finset.sum_le_sum_of_subset_of_nonneg ((supp_subset_range ((natDegree_prod_le _ _).trans_lt (( Finset.sum_le_card_nsmul _ _ _ fun and n=>natDegree_linear_le).trans_lt (by norm_num[n.add_sub_add_right]))))) (by bound)
    norm_num[mul_comm d,mul_assoc,n.add_sub_add_right,←map_pow, Finset.prod_mul_distrib, Finset.prod_add]
    use(Finset.sum_le_sum fun and m=>norm_sum_le _ _).trans ( Finset.sum_comm.trans_le (( Finset.sum_le_sum fun and n=>show _≤(1 : ℝ) from(? _)).trans (by norm_num[n.add_sub_add_right])))
    norm_num[*,←map_prod,←map_pow,coeff_mul_X_pow']
    use if a:_ then(Finset.sum_eq_single_of_mem and.card (( Finset.mem_range_succ_iff.2 a)) fun and I I=>?_).trans_le (by norm_num[←map_prod,norm_prod, *])else(Finset.sum_eq_zero (? _)).trans_le zero_le_one
    · exact (norm_eq_zero.mpr (ite_eq_right_iff.2 (coeff_C_ne_zero ∘Nat.sub_ne_zero_of_lt ∘I.symm.lt_of_le)))
    · use fun and q=>norm_eq_zero.2 (if_neg (a.comp ( Finset.mem_range_succ_iff.1 q).trans'))
  exact (pow_add _ _ _).ge.trans' (h_mul.trans (mul_le_mul h_left h_right (Finset.sum_nonneg (by bound)) (by positivity)))

lemma S_real_eq_sum_roots (n k : ℕ) (hk : 0 < k) :
  (S_real n k : ℂ) = (1 : ℂ) / ↑k * ∑ j ∈ Finset.range k, (P_poly n (Complex.exp (2 * ↑Real.pi * Complex.I * ↑j / ↑k))).coeff k := by
  let' :=Complex.isPrimitiveRoot_exp k fun and =>by simp_all
  norm_num[P_poly, S_real, mul_div_assoc _,Complex.exp_nat_mul,mul_comm (2 *_*( _) : ℂ)]
  norm_num[hk.ne',add_comm (1 : ℂ[X]),←CharP.cast_eq_zero_iff ℂ, mul_pow, mul_div_assoc _,←map_pow, Finset.prod_add] at this⊢
  rw [← Finset.sum_comm, Finset.card_filter,Nat.cast_sum, Finset.sum_congr rfl fun and x => if a:k=and.card then(? _)else(? _), Finset.mul_sum]
  · norm_num[a.symm, and.prod_mul_distrib, and.prod_pow_eq_pow_sum _,pow_right_comm,←map_prod,←map_pow,←this.pow_eq_one_iff_dvd]
    exact (em _).elim (by (norm_num[hk.ne',pow_right_comm _ _ (and.sum _),·])) (if_neg ·▸by (norm_num[geom_sum_eq (by valid),pow_right_comm _ _ (and.sum _),pow_right_comm _ _ k, this.1]))
  · norm_num[a, Ne.symm a, and.prod_mul_distrib,<-map_prod,<-map_pow]

lemma P_poly_one (n k : ℕ) :
  (P_poly n 1).coeff k = (n.choose k : ℂ) := by
  delta P_poly
  norm_num [coeff_one_add_X_pow,n.succ_sub_one]

lemma bound_for_d (n d : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
  n / d + n % d ≤ n / 2 + 1 := by
  nlinarith only[hd,d.div_pos hdn (by valid),n.mod_lt (Nat.le_of_lt hd),n.mod_add_div d,Nat.lt_mul_div_succ n Nat.two_pos]

lemma root_norm_eq_one (k j : ℕ) :
  ‖Complex.exp (2 * ↑Real.pi * Complex.I * ↑j / ↑k)‖ = 1 := by
  exact (Complex.norm_exp _)▸by simp_all

lemma order_of_root (k j : ℕ) (hk : 0 < k) (hj : 0 < j) (hjk : j < k) :
  ∃ d : ℕ, 2 ≤ d ∧ d ≤ k ∧ IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I * ↑j / ↑k)) d := by
  refine match k with|n + 1=>mul_comm (j : ℂ) ( _)▸mul_div_assoc (j : ℂ) _ _▸Complex.exp_nat_mul _ _▸by_contra fun and=>absurd ((Complex.isPrimitiveRoot_exp (n + 1) (nofun)).pow_eq_one_iff_dvd j) ?_
  use fun and' =>and ⟨ _,Ne.lt_of_le' (by valid ∘Nat.eq_zero_of_dvd_of_lt ∘and'.1 ∘orderOf_eq_one_iff.1) (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ?_)),? _,.orderOf _,⟩
  · exact ⟨ _,hk,by rw [pow_right_comm,Complex.isPrimitiveRoot_exp (n + 1) (nofun) |>.1, one_pow]⟩
  · use orderOf_le_of_pow_eq_one hk (by rw [pow_right_comm,Complex.isPrimitiveRoot_exp (n + 1) (nofun) |>.1, one_pow])

lemma S_real_approx_complex (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
  ‖(S_real n k : ℂ) - (1 : ℂ) / ↑k * (n.choose k : ℂ)‖ ≤ (2 : ℝ) * (2 : ℝ) ^ (n / 2) := by
  have h_eq : (S_real n k : ℂ) - (1 : ℂ) / ↑k * (n.choose k : ℂ) = (1 : ℂ) / ↑k * ∑ j ∈ Finset.Ico 1 k, (P_poly n (Complex.exp (2 * ↑Real.pi * Complex.I * ↑j / ↑k))).coeff k := by
    norm_num[P_poly, S_real,mul_comm (2 *_*_ : ℂ),Complex.exp_nat_mul, Finset.sum_Ico_eq_sub _ hk,mul_sub, mul_div_assoc]
    norm_num[add_comm (1 : ℂ[X]),coeff_one_add_X_pow, mul_pow, mul_div_assoc,←pow_mul,←map_pow,←CharP.cast_eq_zero_iff (AlgebraicClosure ℂ),Finset.prod_add]
    norm_num[coeff_X_add_one_pow, mul_div_assoc,pow_mul',←map_prod,←map_pow, Finset.mul_sum, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    refine((congr_arg _) (Finset.card_filter _ _)).trans.comp (Nat.cast_sum _ _).trans (.trans (congr_arg _ (funext fun and=> if a:k=and.card then((symm) ? _)else by norm_num[a, Ne.symm a])) Finset.sum_comm)
    norm_num[<-Finset.mul_sum, mul_div, and.prod_pow, and.prod_pow_eq_pow_sum _,←a,←Complex.isPrimitiveRoot_exp k hk.ne'|>.pow_eq_one_iff_dvd]
    use if a:_ then (by norm_num[a,hk.ne'])else (if_neg a▸.trans (by rw [geom_sum_eq a,pow_right_comm,Complex.isPrimitiveRoot_exp k hk.ne'|>.1]) (by ring))
  have h_norm1 : ‖(1 : ℂ) / ↑k * ∑ j ∈ Finset.Ico 1 k, (P_poly n (Complex.exp (2 * ↑Real.pi * Complex.I * ↑j / ↑k))).coeff k‖ ≤ (1 : ℝ) / ↑k * ∑ j ∈ Finset.Ico 1 k, ‖(P_poly n (Complex.exp (2 * ↑Real.pi * Complex.I * ↑j / ↑k))).coeff k‖ := by
    exact (norm_mul_le_of_le) (by rw [norm_div _,norm_one,Complex.norm_natCast]) ↑(norm_sum_le _ _)
  have h_norm2 : ∀ j ∈ Finset.Ico 1 k, ‖(P_poly n (Complex.exp (2 * ↑Real.pi * Complex.I * ↑j / ↑k))).coeff k‖ ≤ (2 : ℝ) ^ (n / 2 + 1) := by
    intro j hj
    have h_j_pos : 0 < j := by exact ( Finset.mem_Ico.1 ↑(hj)).left
    have h_j_lt : j < k := by exact ( Finset.mem_Ico.1 @hj).2
    have h_ord := order_of_root k j hk h_j_pos h_j_lt
    rcases h_ord with ⟨d, hd2, hdk, hd_prim⟩
    have hd_pos : 0 < d := by omega
    have hdn : d ≤ n := by valid
    have h_norm_ω := root_norm_eq_one k j
    have h_sum_le := P_poly_bound n _ d hd_pos hd_prim h_norm_ω
    have h_le_sum := coeff_le_sum_abs (P_poly n (Complex.exp (2 * ↑Real.pi * Complex.I * ↑j / ↑k))) k
    have h_bound_d := bound_for_d n d hd2 hdn
    exact (h_le_sum.trans h_sum_le).trans (pow_right_mono₀ (by {norm_num}) (by assumption))
  have h_norm : ‖(1 : ℂ) / ↑k * ∑ j ∈ Finset.Ico 1 k, (P_poly n (Complex.exp (2 * ↑Real.pi * Complex.I * ↑j / ↑k))).coeff k‖ ≤ (1 : ℝ) / ↑k * ∑ j ∈ Finset.Ico 1 k, (2 : ℝ) ^ (n / 2 + 1) := by
    apply h_norm1.trans (mul_le_mul_of_nonneg_left ↑( Finset.sum_le_sum (h_norm2)) (by(((positivity)))))
  have h_sum : (1 : ℝ) / ↑k * ∑ j ∈ Finset.Ico 1 k, (2 : ℝ) ^ (n / 2 + 1) = (1 : ℝ) / ↑k * (k - 1 : ℝ) * (2 : ℝ) ^ (n / 2 + 1) := by
    rwa[ Finset.sum_const,nsmul_eq_mul,mul_assoc,Nat.card_Ico,Nat.cast_pred]
  have h_le : (1 : ℝ) / ↑k * (k - 1 : ℝ) * (2 : ℝ) ^ (n / 2 + 1) ≤ (2 : ℝ) * (2 : ℝ) ^ (n / 2) := by
    linear_combination (2 *2^ _)*(div_lt_one (by·bound) ).mpr ↑(sub_one_lt @(k :ℝ) )
  convert (h_norm).trans (h_sum▸(h_le))

lemma S_real_approx (n k : ℕ) :
  |S_real n k - (1 : ℝ) / k * (n.choose k : ℝ)| ≤ 2 * (2 : ℝ) ^ (n / 2) := by
  by_cases hk : k = 0
  · norm_num [hk, S_real,id]
    exact (.trans (by simp_all [ Finset.filter_and, false, Finset.filter_eq']) (show 1 ≤_ by·bound ) )
  · by_cases hkn : k ≤ n
    · have hk_pos : 0 < k := by omega
      have h_c := S_real_approx_complex n k hk_pos hkn
      exact (Complex.norm_real (↑_)).ge.trans (by push_cast[*])
    · simp_all[n.choose_eq_zero_of_lt, S_real]
      exact (.trans (by rw [ Finset.filter_false_of_mem fun and=>by valid ∘ ((1).card_Icc n▸and.card_mono.comp Finset.mem_powerset.1)]) (by use Nat.cast_zero.trans_le (by positivity)))

lemma a_real_diff_bound (n : ℕ) : |a_real n - I_sum n| ≤ (n : ℝ) * (2 : ℝ) ^ ((3:ℝ) * n / 4 + 1) := by
  have h1 : a_real n = ∑ k ∈ Finset.Icc 1 n, S_real n k := a_real_eq_sum_S_real n
  have h2 : I_sum n = ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k * (n.choose k : ℝ) := rfl
  have h3 : |a_real n - I_sum n| ≤ ∑ k ∈ Finset.Icc 1 n, |S_real n k - (1 : ℝ) / k * (n.choose k : ℝ)| := by
    apply dist_sum_sum_le _ _ (@_ : ℕ → ℝ)|>.trans' ((congr_arg _) ((congr_arg₂ _) h1 h2)).le
  have h4 : ∑ k ∈ Finset.Icc 1 n, |S_real n k - (1 : ℝ) / k * (n.choose k : ℝ)| ≤ ∑ k ∈ Finset.Icc 1 n, (2 : ℝ) * (2 : ℝ) ^ (n / 2) := by
    apply Finset.sum_le_sum
    intro k hk
    exact S_real_approx n k
  have h5 : ∑ k ∈ Finset.Icc 1 n, (2 : ℝ) * (2 : ℝ) ^ (n / 2) = (n : ℝ) * (2 : ℝ) ^ (n / 2 + 1) := by
    exact ( Finset.sum_const _).trans (Nat.card_Icc _ _▸by ring!)
  have h6 : (n : ℝ) * (2 : ℝ) ^ (n / 2 + 1) ≤ (n : ℝ) * (2 : ℝ) ^ ((3 : ℝ) * n / 4 + 1) := by
    exact (mul_le_mul_of_nonneg_left) (.trans (by rw [←Real.rpow_natCast,Nat.cast_succ]) (Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith only[Nat.cast_div_le.trans (refl (n/2 : ℝ))]))) n.cast_nonneg
  calc |a_real n - I_sum n| ≤ ∑ k ∈ Finset.Icc 1 n, |S_real n k - (1 : ℝ) / k * (n.choose k : ℝ)| := h3
    _ ≤ ∑ k ∈ Finset.Icc 1 n, (2 : ℝ) * (2 : ℝ) ^ (n / 2) := h4
    _ = (n : ℝ) * (2 : ℝ) ^ (n / 2 + 1) := h5
    _ ≤ (n : ℝ) * (2 : ℝ) ^ ((3 : ℝ) * n / 4 + 1) := h6



lemma a_real_diff : Tendsto (fun n : ℕ => (a_real n - I_sum n) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))) atTop (nhds 0) := by
  have h_bound : ∀ᶠ n : ℕ in atTop, |(a_real n - I_sum n) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))| ≤ ((n : ℝ)^7 * (2 : ℝ) ^ ((3:ℝ) * n / 4 + 1)) / (2 : ℝ) ^ (n + 1) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have h_pos : (0 : ℝ) < ((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6) := by positivity
    rw [abs_div, abs_of_pos h_pos]
    have h1 := a_real_diff_bound n
    have h2 : (n : ℝ) * (2 : ℝ) ^ ((3:ℝ) * n / 4 + 1) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6)) = ((n : ℝ)^7 * (2 : ℝ) ^ ((3:ℝ) * n / 4 + 1)) / (2 : ℝ) ^ (n + 1) := by
      rw [div_div_eq_mul_div, mul_div_assoc]
      ring
    rw [← h2]
    exact div_le_div_of_nonneg_right h1 (le_of_lt h_pos)
  have h_lim : Tendsto (fun n : ℕ => ((n : ℝ)^7 * (2 : ℝ) ^ ((3:ℝ) * n / 4 + 1)) / (2 : ℝ) ^ (n + 1)) atTop (nhds 0) := by
    use((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 7 (.log 2/4) (by positivity)).comp (tendsto_natCast_atTop_atTop)).congr fun and=>symm ((mul_div_assoc _ _ _).trans ((Real.rpow_natCast _ _)▸?_))
    exact (.trans (by rw [←Real.exp_log (pow_pos two_pos _),Real.log_pow, and.cast_succ, Real.rpow_def_of_pos two_pos _,← Real.exp_sub]) (by exact(congr_arg₂ _) (by. (norm_cast)) (congr_arg ↑_ (by·ring))))
  have h_abs_lim : Tendsto (fun n : ℕ => |(a_real n - I_sum n) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))|) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun n => abs_nonneg _)
    · exact h_bound
    · exact h_lim
  have h_iff : Tendsto (fun n : ℕ => (a_real n - I_sum n) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))) atTop (nhds 0) ↔ Tendsto (fun n : ℕ => |(a_real n - I_sum n) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))|) atTop (nhds 0) :=
    tendsto_zero_iff_abs_tendsto_zero (f := (fun n : ℕ => (a_real n - I_sum n) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))))
  exact h_iff.mpr h_abs_lim
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : Tendsto (fun n : ℕ => (a_real n - ((2 : ℝ) ^ (n + 1) / (n : ℝ)) * ((1 : ℝ) + 1 / (n : ℝ) + 3 / ((n : ℝ) ^ 2) + 13 / ((n : ℝ) ^ 3) + 75 / ((n : ℝ) ^ 4) + 541 / ((n : ℝ) ^ 5))) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))) atTop (nhds 0) := by
  -- EVOLVE-BLOCK-START
  have h1 := I_asymp
  have h2 := a_real_diff
  have h3 : Tendsto (fun n : ℕ => (a_real n - I_sum n) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6)) + (I_sum n - ((2 : ℝ) ^ (n + 1) / (n : ℝ)) * ((1 : ℝ) + 1 / (n : ℝ) + 3 / ((n : ℝ) ^ 2) + 13 / ((n : ℝ) ^ 3) + 75 / ((n : ℝ) ^ 4) + 541 / ((n : ℝ) ^ 5))) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))) atTop (nhds (0 + 0)) := Tendsto.add h2 h1
  have h4 : (fun n : ℕ => (a_real n - I_sum n) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6)) + (I_sum n - ((2 : ℝ) ^ (n + 1) / (n : ℝ)) * ((1 : ℝ) + 1 / (n : ℝ) + 3 / ((n : ℝ) ^ 2) + 13 / ((n : ℝ) ^ 3) + 75 / ((n : ℝ) ^ 4) + 541 / ((n : ℝ) ^ 5))) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))) = (fun n : ℕ => (a_real n - ((2 : ℝ) ^ (n + 1) / (n : ℝ)) * ((1 : ℝ) + 1 / (n : ℝ) + 3 / ((n : ℝ) ^ 2) + 13 / ((n : ℝ) ^ 3) + 75 / ((n : ℝ) ^ 4) + 541 / ((n : ℝ) ^ 5))) / (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))) := by
    ext n
    ring
  rw [add_zero] at h3
  rw [h4] at h3
  exact h3
  -- EVOLVE-BLOCK-END
