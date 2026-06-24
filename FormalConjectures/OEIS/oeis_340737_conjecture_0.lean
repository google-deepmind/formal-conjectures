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

/--
A340737: Numerators of a sequence of fractions converging to $e$.
$$a(1) = 3, a(2) = 5$$
For $n > 2$:
$$a(n) = \begin{cases} \left(\frac{n+2}{2}\right) a(n-1) - a(n-2) - \left(\frac{n-2}{2}\right) a(n-3) & \text{if } n \text{ is even} \\ 2 a(n-1) + n a(n-2) & \text{if } n \text{ is odd} \end{cases}$$
-/
noncomputable def A340737 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0 -- Required for total function, O(1,1) suggests 0 is not relevant.
  | 1 => 3
  | 2 => 5
  | n' + 3 => -- n $\ge$ 3
    let n := n' + 3

    let a_nm1 := A340737 (n - 1)
    let a_nm2 := A340737 (n - 2)
    let a_nm3 := A340737 (n - 3)

    if n % 2 = 0 then
      -- n is even, n $\ge$ 4
      let c1 : ℕ := (n + 2) / 2
      let c2 : ℕ := (n - 2) / 2

      -- $a(n) = c_1 \cdot a(n-1) - a(n-2) - c_2 \cdot a(n-3)$.
      -- We use Int.ofNat for safe subtraction, as the result is known to be positive.
      Int.toNat (Int.ofNat c1 * Int.ofNat a_nm1 - Int.ofNat a_nm2 - Int.ofNat c2 * Int.ofNat a_nm3)
    else
      -- n is odd, n $\ge$ 3
      2 * a_nm1 + n * a_nm2
termination_by n

/--
A340738: Denominators of a sequence of fractions converging to $e$.
This sequence is defined by the same recurrence relation as A340737 but with initial values $b(1)=1, b(2)=2$.
$$b(1) = 1, b(2) = 2$$
For $n > 2$:
$$b(n) = \begin{cases} \left(\frac{n+2}{2}\right) b(n-1) - b(n-2) - \left(\frac{n-2}{2}\right) b(n-3) & \text{if } n \text{ is even} \\ 2 b(n-1) + n b(n-2) & \text{if } n \text{ is odd} \end{cases}$$
-/
noncomputable def A340738 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n' + 3 => -- n $\ge$ 3
    let n := n' + 3

    let b_nm1 := A340738 (n - 1)
    let b_nm2 := A340738 (n - 2)
    let b_nm3 := A340738 (n - 3)

    if n % 2 = 0 then
      -- n is even, n $\ge$ 4
      let c1 : ℕ := (n + 2) / 2
      let c2 : ℕ := (n - 2) / 2

      -- $b(n) = c_1 \cdot b(n-1) - b(n-2) - c_2 \cdot b(n-3)$.
      -- We use Int.ofNat for safe subtraction.
      Int.toNat (Int.ofNat c1 * Int.ofNat b_nm1 - Int.ofNat b_nm2 - Int.ofNat c2 * Int.ofNat b_nm3)
    else
      -- n is odd, n $\ge$ 3
      2 * b_nm1 + n * b_nm2
termination_by n

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
noncomputable def u (k : ℕ) (x : ℝ) : ℝ := (x * (1 - x)) ^ k

noncomputable def du (k : ℕ) (x : ℝ) : ℝ := k * (x * (1 - x)) ^ (k - 1) * (1 - 2 * x)

lemma hasDerivAt_u (k : ℕ) (x : ℝ) : HasDerivAt (u k) (du k x) x := by
  delta u Rat _root_.du
  apply(((hasDerivAt_id' @x).mul ((hasDerivAt_id' x).const_sub (1))).congr_deriv (by·ring)).pow

noncomputable def ddu (k : ℕ) (x : ℝ) : ℝ :=
  k * (k - 1) * (x * (1 - x)) ^ (k - 2) * (1 - 2 * x) ^ 2 - 2 * k * (x * (1 - x)) ^ (k - 1)

lemma hasDerivAt_du (k : ℕ) (x : ℝ) : HasDerivAt (du k) (ddu k x) x := by
  delta and ddu _root_.du
  apply((( ((hasDerivAt_id' x).mul ((hasDerivAt_id' x).const_sub (1))).pow @_).const_mul _).mul @(((hasDerivAt_id' x).const_mul 2).const_sub (1))).congr_deriv
  use k.eq_zero_or_pos.elim (by bound) fun and=>.trans (by rw [Nat.cast_pred and,Pi.pow_apply,Pi.mul_apply]) (by ring!)

lemma ddu_eq (k : ℕ) (x : ℝ) : ddu (k + 2) x = (k + 2) * (k + 1) * u k x - 2 * (k + 2) * (2 * k + 3) * u (k + 1) x := by
  norm_num only[push_cast, ddu, u ·]
  exact ( (k + 1).succ_sub_one.symm▸by·ring!)

lemma u_nonneg (k : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ u k x := by
  delta u
  bound

noncomputable def J (k : ℕ) : ℝ := ∫ x in (0:ℝ)..1, u k x * Real.exp x

lemma J_nonneg (k : ℕ) : 0 ≤ J k := by
  delta J
  delta u Real.exp
  use intervalIntegral.integral_nonneg zero_le_one fun and ⟨a, _⟩=>mod_cast by bound

lemma J_zero : J 0 = Real.exp 1 - 1 := by
  rw [J, sub_eq_add_neg]
  norm_num[u,sub_eq_add_neg]

lemma J_one : J 1 = 3 - Real.exp 1 := by
  norm_num[J,Real.exp_eq_exp_ℝ]
  norm_num[u,←Real.exp_eq_exp_ℝ, sub_mul,id]
  norm_num[←sq, sub_mul,((continuous_id'.mul Real.continuous_exp).intervalIntegrable),((continuous_pow _).mul Real.continuous_exp).intervalIntegrable, mul_sub]
  norm_num[intervalIntegral.integral_eq_sub_of_hasDerivAt fun R L=>(((hasDerivAt_id' R).sub_const 1).mul R.hasDerivAt_exp).congr_deriv ↑_, sub_mul,(continuous_id'.mul Real.continuous_exp).intervalIntegrable]
  apply((congr_arg _) ((intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=fun x=>x.exp*(x^2-2*x+2)) (_) (ContinuousOn.intervalIntegrable (by fun_prop))))).trans (by linarith[Real.exp_zero])
  exact (fun R L=>(R.hasDerivAt_exp.mul (by apply((hasDerivAt_pow _ _).sub ((hasDerivAt_id R).const_mul 2)).add_const)).congr_deriv (by ring))

lemma J_le (k : ℕ) : J k ≤ Real.exp 1 / 4 ^ k := by
  delta J Real.exp
  norm_num[u,Complex.exp_re,div_eq_inv_mul, ←inv_pow]
  exact (intervalIntegral.integral_mono_on (by bound) (Continuous.intervalIntegrable (by fun_prop) _ _) intervalIntegrable_const fun and ⟨a, _⟩=> (by bound[sq_nonneg (2 *and-1)]:_≤(1/4)^k*rexp 1)).trans (by simp_all)

lemma J_tendsto_zero : Filter.Tendsto J Filter.atTop (nhds 0) := by
  delta Filter.Tendsto J
  norm_num only [u, intervalIntegral.integral_of_le]
  use((((tendsto_integral_of_dominated_convergence _) fun and=>Continuous.aestronglyMeasurable (by fun_prop)) Real.continuous_exp.integrableOn_Ioc fun and=>ae_restrict_mem (by bound) |>.mono fun and ⟨a, _⟩=>?_) ? _).trans (by rw [ integral_zero])
  · exact (ae_restrict_mem ↑measurableSet_Ioc).mono fun and ⟨a, _⟩=> ((summable_geometric_of_lt_one (by. (bound ) ) (by·linear_combination sq_nonneg (and-2⁻¹))).mul_right @_).tendsto_atTop_zero
  · exact (Real.norm_of_nonneg (by(((bound))))).trans_le ↑(mul_le_of_le_one_left and.exp_nonneg (by(bound)))

lemma deriv_u_exp (k : ℕ) (x : ℝ) : HasDerivAt (fun x => u k x * Real.exp x) ((du k x + u k x) * Real.exp x) x := by
  simp_rw [du, u, add_mul]
  apply((((hasDerivAt_id' x).mul ((hasDerivAt_id' x).const_sub (1))).congr_deriv (by ring)).pow _).mul x.hasDerivAt_exp

lemma deriv_du_exp (k : ℕ) (x : ℝ) : HasDerivAt (fun x => du k x * Real.exp x) ((ddu k x + du k x) * Real.exp x) x := by
  simp_rw [du, add_mul,ddu]
  apply(((((((hasDerivAt_id' x).mul ((hasDerivAt_id' x).const_sub (1))).pow _).const_mul _).mul<|((hasDerivAt_id' x).const_mul 2).const_sub 1)).mul x.hasDerivAt_exp).congr_deriv ∘symm
  exact (symm (.trans (by rw [Pi.mul_apply,Pi.mul_apply,Pi.pow_apply,Pi.mul_apply]) (by cases k with|zero=>ring|succ=>exact (.trans (by rw [Nat.cast_pred (by bound)]) (by ring!)))))

lemma int_deriv_u_exp (k : ℕ) (hk : 1 ≤ k) : ∫ x in (0:ℝ)..1, (du k x + u k x) * Real.exp x = 0 := by
  delta u du
  replace R M:=((((hasDerivAt_id' (M : ℝ))).mul ((hasDerivAt_id' M).const_sub (1))).pow k).mul M.hasDerivAt_exp
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (@fun A B=>(R A).congr_deriv.comp (.trans (by rw [Pi.pow_apply,Pi.mul_apply])) (by ring)) (Continuous.intervalIntegrable (by fun_prop) _ _)).trans (by norm_num[mt hk.trans_eq])

lemma int_deriv_du_exp (k : ℕ) (hk : 2 ≤ k) : ∫ x in (0:ℝ)..1, (ddu k x + du k x) * Real.exp x = 0 := by
  simp_rw [du, add_mul,comm, ddu]
  have R M:=((((hasDerivAt_id' (M:ℝ)).mul ((hasDerivAt_id' M).const_sub (1))).pow<|k-1).mul (((hasDerivAt_id' M).const_mul 2).const_sub 1)).mul M.hasDerivAt_exp
  use(((intervalIntegral.integral_eq_sub_of_hasDerivAt fun and x =>((R and).const_mul ↑k).congr_deriv.comp (.trans (by rw [Pi.mul_apply,Pi.mul_apply,Pi.pow_apply,Pi.mul_apply,Nat.cast_pred (by valid)])) (by ring!)) ? _).trans (? _)).symm
  · apply Continuous.intervalIntegrable<|by fun_prop
  · norm_num[Nat.sub_ne_zero_of_lt ↑hk]

lemma int_ddu_eq_J (k : ℕ) (hk : 2 ≤ k) : ∫ x in (0:ℝ)..1, ddu k x * Real.exp x = J k := by
  delta and J ddu
  delta u
  rw [←sub_eq_zero, ←intervalIntegral.integral_sub ↑(Continuous.intervalIntegrable (by·fun_prop) _ _) ↑(Continuous.intervalIntegrable (by. (fun_prop) ) _ _), Eq.comm]
  have R M:=(((hasDerivAt_id' (M:ℝ)).mul ((hasDerivAt_id' M).const_sub (1))).pow<|k-1).mul (((hasDerivAt_id' M).const_mul 2).const_sub 1)|>.mul M.hasDerivAt_exp
  have R M := ( (R M).const_mul ↑ k).sub.comp ( ((hasDerivAt_id' M).mul ((hasDerivAt_id' M).const_sub (1))).pow k).mul M.hasDerivAt_exp
  refine(((intervalIntegral.integral_eq_sub_of_hasDerivAt fun and x => (R and).congr_deriv.comp (.trans (by rw [Pi.mul_apply,Pi.mul_apply,Pi.pow_apply,Pi.pow_apply,Pi.mul_apply,Nat.cast_pred (by valid)])) (by ring!)) ? _).trans (? _)).symm
  · apply(Continuous.intervalIntegrable (by((fun_prop))))
  · norm_num[mt hk.trans_eq,Nat.sub_ne_zero_of_lt hk]

lemma J_rec (k : ℕ) : J (k + 2) = (k + 2) * (k + 1) * J k - 2 * (k + 2) * (2 * k + 3) * J (k + 1) := by
  change (star _) = _*( star _) -_*(star _)
  norm_num[u, ← intervalIntegral.integral_of_le _,two_mul,add_assoc]
  use(add_zero _).trans ( show _ = _*(_+0: ℝ)-_*(_+0) from symm (.trans (by rw [add_zero, add_zero,←intervalIntegral.integral_const_mul,←intervalIntegral.integral_const_mul]) ?_))
  rw [← intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (Continuous.intervalIntegrable (by fun_prop) _ _), ← sub_eq_zero, ← intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)]
  · have R M:=(((hasDerivAt_id' (M:ℝ)).mul ((hasDerivAt_id' M).const_sub (1))).pow (k+2)).mul M.hasDerivAt_exp
    have R M:=((((hasDerivAt_id' (M:ℝ)).mul ((hasDerivAt_id' M).const_sub (1))).pow (k + 1)).mul M.hasDerivAt_exp).mul ((hasDerivAt_id' M).sub_const (@1/2))
    push_cast[Pi.mul_apply,Pi.pow_apply]at*
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (@ fun and x =>(((R and).const_mul (2 *(k+2): ℝ)).neg.sub (by apply_rules)).congr_deriv (by ring)) (Continuous.intervalIntegrable (by fun_prop) _ _)).trans (by {norm_num})
  · apply (Continuous.intervalIntegrable (by ·fun_prop ) )

noncomputable def seqU : ℕ → ℝ
| 0 => 1
| 1 => 3
| (k+2) => (4 * (k + 2 : ℝ) - 2) * seqU (k+1) + seqU k

noncomputable def seqV : ℕ → ℝ
| 0 => 1
| 1 => 1
| (k+2) => (4 * (k + 2 : ℝ) - 2) * seqV (k+1) + seqV k

lemma A_match_all (n : ℕ) :
  (A340737 (2*n + 1) : ℝ) = seqU (n + 1) ∧
  (A340737 (2*n + 2) : ℝ) = ((2*n + 3) * seqU (n + 1) + seqU n) / 2 := by
  induction n with
  | zero => norm_num only [seqU, A340737, and_self_iff]
  | succ n ih => simp_all![seqU, mul_add, add_assoc, add_mul,add_div]
                 simp_all![(A340737 ·)]
                 ring_nf at*
                 norm_num[*, add_div]
                 simp_all[(by valid: (4+n*2 : Int)/2=2+n)]
                 norm_cast at*
                 exact (.trans ( by aesop) (.symm (.trans ( by aesop) (by ring))))

lemma B_match_all (n : ℕ) :
  (A340738 (2*n + 1) : ℝ) = seqV (n + 1) ∧
  (A340738 (2*n + 2) : ℝ) = ((2*n + 3) * seqV (n + 1) + seqV n) / 2 := by
  induction n with
  | zero => norm_num[seqV, A340738]
  | succ n ih => simp_all![seqV, mul_add, add_assoc, add_div]
                 norm_num[ih, mul_div_assoc _,add_sub_assoc, A340738]
                 simp_all[add_assoc]
                 ring_nf at ih⊢
                 norm_cast at*
                 rw [←Int.cast_natCast,Int.toNat_of_nonneg]
                 · use⟨⟩,.trans (by rw [ (by valid:_/2=2+n)]) (.trans ( by aesop) (.symm (.trans ( by aesop) (by ring))))
                 · exact (by valid: (4+n*2)/2=2+n).symm▸ (by valid: (2+n*2)/2=1+n).symm▸Nat.mul_add _ _ _▸Nat.mul_comm n _▸(le_or_gt _ _).elim (Int.subNatNat_of_le ·▸by valid) (by grind)

lemma seqV_ge_one (k : ℕ) : (1 : ℝ) ≤ seqV k := by
  delta seqV
  induction k using@Nat.twoStepInduction with|zero | one=>rfl | more=>exact (le_add_of_nonneg_of_le) (mul_nonneg (by {linarith}) ↑(zero_le_one.trans (by assumption))) (by assumption)

noncomputable def seqD (k : ℕ) : ℝ := (-1 : ℝ)^k * k.factorial * (seqV k * Real.exp 1 - seqU k)

lemma seqD_zero : seqD 0 = Real.exp 1 - 1 := by
  norm_num[seqD]
  norm_num [seqV,seqU]

lemma seqD_one : seqD 1 = 3 - Real.exp 1 := by
  delta Real.exp seqD
  norm_num [seqU, false,seqV]

lemma seqD_rec (k : ℕ) : seqD (k + 2) = (k + 2) * (k + 1) * seqD k - 2 * (k + 2) * (2 * k + 3) * seqD (k + 1) := by
  zify [seqD]
  push_cast[seqU, two_mul,seqV,·!]
  ring

lemma J_eq_seqD_both (k : ℕ) : J k = seqD k ∧ J (k + 1) = seqD (k + 1) := by
  induction k with
  | zero => norm_num [seqD, J]
            simp_all![u]
            norm_num[←sq, mul_sub, sub_mul,Continuous.intervalIntegrable,continuous_id'.mul Real.continuous_exp,(continuous_pow _).mul Real.continuous_exp]
            norm_num[intervalIntegral.integral_eq_sub_of_hasDerivAt fun R L=>(((hasDerivAt_id' R).sub_const 1).mul R.hasDerivAt_exp).congr_deriv ↑_, sub_mul,(continuous_id'.mul Real.continuous_exp).intervalIntegrable]
            apply ((congr_arg _) ((intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=fun x=>x.exp*(x^2-2*x+2)) (_) (ContinuousOn.intervalIntegrable (by fun_prop))))).trans (by. (norm_num [sub_sub_eq_add_sub]))
            exact (fun R L=>(R.hasDerivAt_exp.mul (by apply((hasDerivAt_pow (2) R).sub ((hasDerivAt_id R).const_mul 2)).add_const)).congr_deriv (by ring))
  | succ k ih =>
    constructor
    · exact ih.2
    · rw [J_rec k, seqD_rec k, ih.1, ih.2]

lemma J_eq_seqD (k : ℕ) : J k = seqD k := by
  exact (J_eq_seqD_both k).1

lemma seqD_tendsto_zero : Filter.Tendsto seqD Filter.atTop (nhds 0) := by
  have h_eq : seqD = J := by
    ext k
    exact (J_eq_seqD k).symm
  rw [h_eq]
  exact J_tendsto_zero

lemma tendsto_abs_zero_of_tendsto_zero {f : ℕ → ℝ} (h : Filter.Tendsto f Filter.atTop (nhds 0)) : Filter.Tendsto (fun n => |f n|) Filter.atTop (nhds 0) := by
  apply (@tendsto_norm_zero).comp h

lemma tendsto_zero_of_abs_le {f g : ℕ → ℝ} (h_le : ∀ n, |f n| ≤ g n) (h_g : Filter.Tendsto g Filter.atTop (nhds 0)) : Filter.Tendsto f Filter.atTop (nhds 0) := by
  use squeeze_zero_norm h_le h_g

noncomputable def seqE (k : ℕ) : ℝ := seqU k - seqV k * Real.exp 1

lemma seqD_eq_seqE (k : ℕ) : seqD k = (-1 : ℝ)^(k+1) * k.factorial * seqE k := by
  unfold seqD seqE
  have h1 : (-1 : ℝ)^k * (seqV k * Real.exp 1 - seqU k) = (-1 : ℝ)^(k+1) * seqE k := by
    norm_num[seqE,seqU, true,seqV, false,pow_succ]
    ring
  ring1

lemma abs_seqD_eq_fact_mul_abs_seqE (k : ℕ) : |seqD k| = k.factorial * |seqE k| := by
  delta abs seqD seqE
  exact (abs_mul _ _).trans (congr_arg₂ _ (by simp_all[abs_mul])<|abs_sub_comm _ _)

lemma abs_seqE_le_abs_seqD (k : ℕ) : |seqE k| ≤ |seqD k| := by
  delta abs seqD seqE
  exact (abs_sub_comm _ _).trans_le ((le_mul_of_one_le_left (@norm_nonneg ℝ _ _) (by simp_all[abs_mul,k.factorial_pos.nat_succ_le])).trans (abs_mul _ _).ge)

lemma seqE_tendsto_zero : Filter.Tendsto seqE Filter.atTop (nhds 0) := by
  have h_g : Filter.Tendsto (fun k => |seqD k|) Filter.atTop (nhds 0) := tendsto_abs_zero_of_tendsto_zero seqD_tendsto_zero
  exact tendsto_zero_of_abs_le abs_seqE_le_abs_seqD h_g

lemma tendsto_seqE_div_seqV_zero : Filter.Tendsto (fun k => seqE k / seqV k) Filter.atTop (nhds 0) := by
  have h_g : Filter.Tendsto (fun k => |seqE k|) Filter.atTop (nhds 0) := tendsto_abs_zero_of_tendsto_zero seqE_tendsto_zero
  have h_le : ∀ k, |seqE k / seqV k| ≤ |seqE k| := by
    intro k
    rw [abs_div]
    have hV : 1 ≤ |seqV k| := by
      have := seqV_ge_one k
      exact le_trans this (le_abs_self _)
    have hl : |seqE k| / |seqV k| ≤ |seqE k| / 1 := div_le_div_of_nonneg_left (abs_nonneg _) (zero_lt_one) hV
    rw [div_one] at hl
    exact hl
  exact tendsto_zero_of_abs_le h_le h_g

lemma seqU_eq (k : ℕ) : seqU k = seqV k * Real.exp 1 + seqE k := by
  unfold seqE
  ring

lemma seqU_div_seqV_eq (k : ℕ) : seqU k / seqV k = Real.exp 1 + seqE k / seqV k := by
  rw [seqU_eq k]
  have hV : seqV k ≠ 0 := by
    have := seqV_ge_one k
    linarith
  rw [add_div, mul_div_cancel_left₀ _ hV]

lemma tendsto_seqU_div_seqV : Filter.Tendsto (fun k => seqU k / seqV k) Filter.atTop (nhds (Real.exp 1)) := by
  have h_eq : (fun k => seqU k / seqV k) = (fun k => Real.exp 1 + seqE k / seqV k) := by
    ext k
    exact seqU_div_seqV_eq k
  rw [h_eq]
  have ht : Filter.Tendsto (fun k => Real.exp 1 + seqE k / seqV k) Filter.atTop (nhds (Real.exp 1 + 0)) :=
    Filter.Tendsto.add tendsto_const_nhds tendsto_seqE_div_seqV_zero
  rw [add_zero] at ht
  exact ht

lemma tendsto_shift {α : Type*} {f : ℕ → α} {l : Filter α} (h : Filter.Tendsto f Filter.atTop l) : Filter.Tendsto (fun k => f (k + 1)) Filter.atTop l := by
  rwa[l.tendsto_add_atTop_iff_nat]

lemma A_even_eq_seqU (k : ℕ) : (A340737 (2*k + 2) : ℝ) = ((2*k + 3) * seqU (k + 1) + seqU k) / 2 := by
  exact (A_match_all k).2

lemma B_even_eq_seqV (k : ℕ) : (A340738 (2*k + 2) : ℝ) = ((2*k + 3) * seqV (k + 1) + seqV k) / 2 := by
  exact (B_match_all k).2

lemma A_even_div_B_even_eq (k : ℕ) :
  (A340737 (2*k + 2) : ℝ) / (A340738 (2*k + 2) : ℝ) =
  ((2*k + 3) * seqU (k + 1) + seqU k) / ((2*k + 3) * seqV (k + 1) + seqV k) := by
  have h1 := A_even_eq_seqU k
  have h2 := B_even_eq_seqV k
  rw [h1, h2]
  push_cast
  have h_half : ∀ a b : ℝ, (a / 2) / (b / 2) = a / b := by
    exact fun and x =>by ring
  exact h_half _ _

lemma A_even_div_B_even_eq_e_add (k : ℕ) :
  (A340737 (2*k + 2) : ℝ) / (A340738 (2*k + 2) : ℝ) =
  Real.exp 1 + ((2*(k:ℝ) + 3) * seqE (k + 1) + seqE k) / ((2*(k:ℝ) + 3) * seqV (k + 1) + seqV k) := by
  have heq : (A340737 (2*k + 2) : ℝ) / (A340738 (2*k + 2) : ℝ) = ((2*(k:ℝ) + 3) * seqU (k + 1) + seqU k) / ((2*(k:ℝ) + 3) * seqV (k + 1) + seqV k) := by
    have h1 := A_even_div_B_even_eq k
    push_cast at h1
    exact h1
  rw [heq]
  have hU1 := seqU_eq (k + 1)
  have hU0 := seqU_eq k
  rw [hU1, hU0]
  have hd : (2 * (k:ℝ) + 3) * (seqV (k + 1) * Real.exp 1 + seqE (k + 1)) + (seqV k * Real.exp 1 + seqE k) =
    ((2 * (k:ℝ) + 3) * seqV (k + 1) + seqV k) * Real.exp 1 + ((2 * (k:ℝ) + 3) * seqE (k + 1) + seqE k) := by
    ring
  rw [hd]
  have hV : (2 * (k:ℝ) + 3) * seqV (k + 1) + seqV k ≠ 0 := by
    delta Ne seqV
    use ne_of_gt<|add_pos (mul_pos (by positivity) (by induction (k + 1) using Nat.twoStepInduction with|zero|one=>norm_num| more=>use add_pos (by bound) (by valid))) (k.strongRec fun and i=>? _)
    match and with|0|1=>apply one_pos | S+2=>use add_pos (mul_pos (by linarith only) (i ( _) (by constructor))) (i S (by repeat constructor))
  rw [add_div, mul_div_cancel_left₀ _ hV]

lemma abs_even_error_term_le (k : ℕ) :
  |((2 * (k:ℝ) + 3) * seqE (k + 1) + seqE k) / ((2 * (k:ℝ) + 3) * seqV (k + 1) + seqV k)| ≤ |seqE (k + 1)| + |seqE k| := by
  delta seqE seqV
  use(abs_div _ _).trans_le (div_le_of_le_mul₀ (abs_nonneg _) (by bound) (.trans ( (@norm_add_le_of_le ℝ) (norm_mul_le_of_le ((abs_of_nonneg (by linarith)).le) (le_rfl)) (le_rfl)) ?_))
  use(mul_le_mul_of_nonneg_left ((le_mul_of_one_le_right (by linarith) ? _).trans (.trans (le_add_of_nonneg_right ? _) le_sup_left)) (by bound)).trans' ?_
  · induction (k + 1) using Nat.twoStepInduction with|zero|one =>rfl| more =>exact (.trans (by bound) (le_add_of_nonneg_right (zero_le_one.trans (by assumption))))
  · induction k using Nat.twoStepInduction with |zero | one=>exact (zero_le_one) | more=>exact add_nonneg ↑(mul_nonneg (by(linarith)) (by assumption) ) (by assumption')
  · use(@mul_comm ℝ) _ _▸.trans (by bound) (add_mul _ _ _).ge

lemma tendsto_even_error_term : Filter.Tendsto (fun k : ℕ => ((2*(k:ℝ) + 3) * seqE (k + 1) + seqE k) / ((2*(k:ℝ) + 3) * seqV (k + 1) + seqV k)) Filter.atTop (nhds 0) := by
  have hE_zero : Filter.Tendsto seqE Filter.atTop (nhds 0) := seqE_tendsto_zero
  have hE_abs : Filter.Tendsto (fun k : ℕ => |seqE k|) Filter.atTop (nhds 0) := tendsto_abs_zero_of_tendsto_zero hE_zero
  have hE_abs_shift : Filter.Tendsto (fun k : ℕ => |seqE (k + 1)|) Filter.atTop (nhds 0) := tendsto_shift hE_abs
  have h_sum : Filter.Tendsto (fun k : ℕ => |seqE (k + 1)| + |seqE k|) Filter.atTop (nhds (0 + 0)) := Filter.Tendsto.add hE_abs_shift hE_abs
  rw [add_zero] at h_sum
  exact tendsto_zero_of_abs_le abs_even_error_term_le h_sum

lemma tendsto_A_even_div_B_even : Filter.Tendsto (fun k => (A340737 (2*k + 2) : ℝ) / (A340738 (2*k + 2) : ℝ)) Filter.atTop (nhds (Real.exp 1)) := by
  have h_eq : (fun (k:ℕ) => (A340737 (2*k + 2) : ℝ) / (A340738 (2*k + 2) : ℝ)) =
              (fun (k:ℕ) => Real.exp 1 + ((2 * (k:ℝ) + 3) * seqE (k + 1) + seqE k) / ((2 * (k:ℝ) + 3) * seqV (k + 1) + seqV k)) := by
    ext k
    exact A_even_div_B_even_eq_e_add k
  rw [h_eq]
  have ht : Filter.Tendsto (fun (k:ℕ) => Real.exp 1 + ((2 * (k:ℝ) + 3) * seqE (k + 1) + seqE k) / ((2 * (k:ℝ) + 3) * seqV (k + 1) + seqV k)) Filter.atTop (nhds (Real.exp 1 + 0)) :=
    Filter.Tendsto.add tendsto_const_nhds tendsto_even_error_term
  rw [add_zero] at ht
  exact ht

lemma tendsto_even_odd_pos {α : Type*} [TopologicalSpace α] {f : ℕ → α} {l : Filter α}
  (hodd : Filter.Tendsto (fun k => f (2 * k + 1)) Filter.atTop l)
  (heven : Filter.Tendsto (fun k => f (2 * k + 2)) Filter.atTop l) :
  Filter.Tendsto f Filter.atTop l := by
  simp_rw [l.tendsto_atTop']at*
  exact (fun A B=>(hodd A B).elim ((heven A B).elim fun and h a s=>by use (2 * (and+ a))+3,fun A B=>match A with | S+1=> S.even_or_odd'.elim fun and true => true.elim (.▸s and (by valid)) (.▸h and (by valid))))

-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : Filter.Tendsto (fun n : ℕ => (A340737 n : ℝ) / (A340738 n : ℝ)) Filter.atTop (nhds (Real.exp 1)) := by
  -- EVOLVE-BLOCK-START
  have h_odd : Filter.Tendsto (fun k => (A340737 (2 * k + 1) : ℝ) / (A340738 (2 * k + 1) : ℝ)) Filter.atTop (nhds (Real.exp 1)) := by
    have h_eq : (fun k => (A340737 (2 * k + 1) : ℝ) / (A340738 (2 * k + 1) : ℝ)) = (fun k => seqU (k + 1) / seqV (k + 1)) := by
      ext k
      have h1 : (A340737 (2 * k + 1) : ℝ) = seqU (k + 1) := (A_match_all k).1
      have h2 : (A340738 (2 * k + 1) : ℝ) = seqV (k + 1) := (B_match_all k).1
      rw [h1, h2]
    rw [h_eq]
    exact tendsto_shift tendsto_seqU_div_seqV
  exact tendsto_even_odd_pos h_odd tendsto_A_even_div_B_even
  -- EVOLVE-BLOCK-END
