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




open Rat

/--
Recursive function to compute $A_k(n)$, the denominator tail $k - \frac{k+1}{A_{k+1}(n)}$.
The base case is at $k = n - 1$, where $A_{n-1} = (n-1) - \frac{n}{n+4}$.
-/
noncomputable def continued_fraction_tail (n : ℕ) : ℕ → ℚ
| k =>
  if n ≥ 4 then
    if k = n - 1 then
      (n - 1 : ℚ) - (n : ℚ) / (n + 4 : ℚ)
    else if 3 ≤ k ∧ k < n - 1 then
      let k_succ_val := continued_fraction_tail n (k + 1)
      -- Division by zero handling for total function definition
      if k_succ_val = 0 then 0 else
        (k : ℚ) - (k + 1 : ℚ) / k_succ_val
    else
      0
  else
    0
termination_by k => n - k

/--
The total value of the continued fraction $C_n$.
-/
noncomputable def continued_fraction_val (n : ℕ) : ℚ :=
  if n ≤ 2 then
    0
  else if n = 3 then
    -- Formula for n=3: 1 / (2 - 3 / (3 + 4)) = 7/11
    let val : ℚ := 2 - 3 / 7
    if val = 0 then 0 else 1 / val
  else -- n ≥ 4
    let A3 := continued_fraction_tail n 3
    let val : ℚ := 2 - 3 / A3

    -- Division by zero check for the final rational value
    if val = 0 then 0 else 1 / val

/--
A372761: Denominator of the continued fraction
$$ \frac{1}{2 - \frac{3}{3 - \frac{4}{4 - \frac{5}{\dots - \frac{n-1}{(n-1) - \frac{n}{n+4}}}}}} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n < 3 then 0 -- Sequence starts at n=3.
  else (continued_fraction_val n).den

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
def sum_fact : ℕ → ℕ
| 0 => 0
| k + 1 => sum_fact k + k.factorial

def IntQ2 (n : ℕ) : ℤ :=
  (5 * (n : ℤ) - 4) * sum_fact (n - 3) + ((n : ℤ) - 1) * (n - 3).factorial * ((n : ℤ) + 4)

noncomputable def Q_explicit (n k : ℕ) : ℚ :=
  if k = 0 then 0
  else if k = 1 then 5 * (n : ℚ) - 4
  else
    (k - 1 : ℚ) * (IntQ2 n - (5 * (n : ℚ) - 4) * sum_fact (k - 2)) / (k.factorial : ℚ)

lemma Q_explicit_recurrence (n k : ℕ) (hk : k ≥ 2) :
  Q_explicit n (k - 1) = k * Q_explicit n k - (k + 1) * Q_explicit n (k + 1) := by
  delta Q_explicit
  match k with|(2) | S+3=>_
  · norm_num[sum_fact,div_eq_inv_mul, ←mul_assoc]
  simp_all![ (by·norm_cast: (S+3 : Rat)+1 ≠0), mul_div, mul_div_mul_left _ _]
  exact (mul_div_mul_left _ _ (by ·norm_cast)).symm.trans (.trans (congr_arg ↑(· / _) (by·ring)) ( sub_div _ _ _))

lemma tail_eq_base (n : ℕ) (hn : n ≥ 4) :
  continued_fraction_tail n (n - 1) = Q_explicit n (n - 2) / Q_explicit n (n - 1) := by
  delta Q_explicit continued_fraction_tail Rat
  refine WellFounded.Nat.fix_eq _ _ _▸match n with | S+4 =>(dif_pos @hn).trans.comp (dif_pos rfl ).trans (.trans (sub_div' (by·norm_cast)) ? _)
  push_cast[sum_fact,IntQ2,.!,add_sub_assoc,div_div_div_eq]
  exact (div_eq_div_iff (by positivity) (ne_of_eq_of_ne (by rw [add_sub_cancel]) (by positivity))).2 (by ring)

lemma tail_eq_desc_0 (n : ℕ) (hn : n ≥ 4) :
  continued_fraction_tail n (n - 1) = Q_explicit n (n - 2) / Q_explicit n (n - 1) := by
  delta Q_explicit continued_fraction_tail Rat
  refine WellFounded.Nat.fix_eq _ _ _▸match n with | S+4 =>(dif_pos @hn).trans.comp (dif_pos rfl ).trans (.trans (sub_div' (by·norm_cast)) ? _)
  push_cast[sum_fact,IntQ2,.!,add_sub_assoc,div_div_div_eq]
  exact (div_eq_div_iff (by positivity) (ne_of_eq_of_ne (by rw [add_sub_cancel]) (by positivity))).2 (by ring)

lemma Q_explicit_pos (n k : ℕ) (hn : n ≥ 4) (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) :
  Q_explicit n k > 0 := by
  simp_rw [ ·≥ ·,Q_explicit] at hn⊢
  norm_num [sum_fact,IntQ2,mt hk1.trans_eq]
  use if a:_ then (if_pos a▸sub_pos.2 (mod_cast (by valid)))else (if_neg a▸div_pos (mul_pos (sub_pos.2 (mod_cast (by valid))) (sub_pos.2 (lt_add_of_le_of_pos ?_ ?_))) (by positivity))
  · exact (mul_le_mul_of_nonneg_left) (mod_cast(k-2).le_induction le_rfl (fun A B=>le_add_right) (n-3) (by valid)) ( sub_nonneg.2 (mod_cast (by valid)))
  · match sub_pos.mpr (mod_cast (by valid): (n :ℚ) >1) with | S=>positivity

lemma Q_explicit_nz (n k : ℕ) (hn : n ≥ 4) (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) :
  Q_explicit n k ≠ 0 := by
  simp_rw [Nat.succ_le, Q_explicit] at hn⊢
  delta IntQ2 Ne sum_fact
  norm_num[mt hk1.trans_eq, sub_eq_zero,mt (lt_mul_right _ _).trans_eq,hn.trans',k.factorial_ne_zero,ite_eq_iff]
  use (⟨.,(lt_add_of_le_of_pos (mul_le_mul_of_nonneg_left (Nat.cast_le.2 ↑((k-2).le_induction le_rfl (fun a s=>le_add_right) (n-3) (by valid))) (sub_nonneg.2 (mod_cast (by valid)))) ?_).ne'⟩)
  match sub_pos.2 (mod_cast (by valid):(n:ℚ) >1) with | S=>positivity

lemma tail_unfold (n k : ℕ) (hn : n ≥ 4) (hk1 : 3 ≤ k) (hk2 : k < n - 1)
  (hsucc : continued_fraction_tail n (k + 1) ≠ 0) :
  continued_fraction_tail n k = (k : ℚ) - (k + 1 : ℚ) / continued_fraction_tail n (k + 1) := by
  delta continued_fraction_tail at*
  refine WellFounded.Nat.fix_eq _ _ _▸(dif_pos hn).trans.comp (dif_neg (@hk2).ne).trans ((dif_pos (by use @hk1)).trans (dif_neg hsucc))

lemma tail_eq_desc_step_aux (n k : ℕ) (hn : n ≥ 4) (hk1 : 3 ≤ k) (hk2 : k < n - 1)
  (ih : continued_fraction_tail n (k + 1) = Q_explicit n k / Q_explicit n (k + 1))
  (hq1 : Q_explicit n k ≠ 0) (hq2 : Q_explicit n (k + 1) ≠ 0) :
  (k : ℚ) - (k + 1 : ℚ) / continued_fraction_tail n (k + 1) = Q_explicit n (k - 1) / Q_explicit n k := by
  simp_all only[Ne, sub_div' ↑(hq1),div_div_eq_mul_div, true, Q_explicit]
  use(sub_div' hq1).trans (congr_arg (./ _)<|match k with | S+3=>? _)
  norm_num[sum_fact,mul_div, mul_div_mul_left _,add_sub_assoc, add_assoc, add_eq_zero_iff_of_nonneg _,.!,Nat.succ_inj.eq,Nat.succ_sub_succ_eq_sub _ _]
  exact (mul_div_mul_left _ _ (by ·norm_cast: ( S : Rat)+2≠0))▸by ring

lemma tail_eq_desc (n d : ℕ) (hn : n ≥ 4) (hd : d ≤ n - 4) :
  continued_fraction_tail n (n - 1 - d) = Q_explicit n (n - 2 - d) / Q_explicit n (n - 1 - d) := by
  induction d with
  | zero =>
    have eq1 : n - 1 - 0 = n - 1 := by omega
    have eq2 : n - 2 - 0 = n - 2 := by omega
    rw [eq1, eq2]
    exact tail_eq_desc_0 n hn
  | succ d ih =>
    have hd_ih : d ≤ n - 4 := by omega
    have ih_spec := ih hd_ih
    set k := n - 2 - d
    have hk1 : 3 ≤ k := by omega
    have hk2 : k < n - 1 := by omega
    have eq_k : n - 1 - (d + 1) = k := by omega
    have eq_k1 : n - 1 - d = k + 1 := by omega
    have eq_km1 : n - 2 - (d + 1) = k - 1 := by omega
    rw [eq_k1] at ih_spec
    rw [eq_k, eq_km1]
    have hq1 := Q_explicit_nz n k hn (by omega) (by omega)
    have hq2 := Q_explicit_nz n (k + 1) hn (by omega) (by omega)
    have hsucc : continued_fraction_tail n (k + 1) ≠ 0 := by
      rw [ih_spec]
      intro h_zero
      have h_zero_num : Q_explicit n k = 0 := by
        exact (div_eq_zero_iff.mp h_zero).resolve_right (by exact_mod_cast hq2)
      exact hq1 h_zero_num
    have h_unfold := tail_unfold n k hn hk1 hk2 hsucc
    have h_step := tail_eq_desc_step_aux n k hn hk1 hk2 ih_spec hq1 hq2
    rw [h_unfold]
    exact h_step

lemma tail_eq (n k : ℕ) (hn : n ≥ 4) (hk1 : 3 ≤ k) (hk2 : k ≤ n - 1) :
  continued_fraction_tail n k = Q_explicit n (k - 1) / Q_explicit n k := by
  have hd : n - 1 - k ≤ n - 4 := by omega
  have h_desc := tail_eq_desc n (n - 1 - k) hn hd
  have eq1 : n - 1 - (n - 1 - k) = k := by omega
  have eq2 : n - 2 - (n - 1 - k) = k - 1 := by omega
  rw [eq1, eq2] at h_desc
  exact h_desc

lemma val_eq_unfold (n : ℕ) (hn : n ≥ 4) (ha3 : continued_fraction_tail n 3 ≠ 0)
  (hval : 2 - 3 / continued_fraction_tail n 3 ≠ 0) :
  continued_fraction_val n = 1 / (2 - 3 / continued_fraction_tail n 3) := by
  show(star _) = _
  match n with | S+4 =>apply (if_neg hval)

lemma Q2_eq (n : ℕ) : Q_explicit n 2 = (IntQ2 n : ℚ) / 2 := by
  norm_num[ Q_explicit,IntQ2]

lemma val_eq_aux (n : ℕ) (hn : n ≥ 4)
  (ha3 : continued_fraction_tail n 3 = Q_explicit n 2 / Q_explicit n 3)
  (hq2 : Q_explicit n 2 ≠ 0) (hq3 : Q_explicit n 3 ≠ 0)
  (hq1 : Q_explicit n 1 = 2 * Q_explicit n 2 - 3 * Q_explicit n 3) :
  1 / (2 - 3 / continued_fraction_tail n 3) = Q_explicit n 2 / Q_explicit n 1 := by
  rwa[hq1,ha3,div_div_eq_mul_div, sub_div', (one_div_div)]

lemma val_eq (n : ℕ) (hn : n ≥ 4) :
  continued_fraction_val n = (Q_explicit n 2) / (Q_explicit n 1) := by
  have ha3 : continued_fraction_tail n 3 = Q_explicit n 2 / Q_explicit n 3 := tail_eq n 3 hn (by omega) (by omega)
  have hq1_nz : Q_explicit n 1 ≠ 0 := Q_explicit_nz n 1 hn (by omega) (by omega)
  have hq2_nz : Q_explicit n 2 ≠ 0 := Q_explicit_nz n 2 hn (by omega) (by omega)
  have hq3_nz : Q_explicit n 3 ≠ 0 := Q_explicit_nz n 3 hn (by omega) (by omega)
  have hq1_eq : Q_explicit n 1 = 2 * Q_explicit n 2 - 3 * Q_explicit n 3 := by
    have h_rec := Q_explicit_recurrence n 2 (by omega)
    have eq1 : 2 - 1 = 1 := rfl
    have eq2 : 2 + 1 = 3 := rfl
    rw [eq1, eq2] at h_rec
    norm_num at h_rec
    exact h_rec
  have haux := val_eq_aux n hn ha3 hq2_nz hq3_nz hq1_eq
  have ha3_nz : continued_fraction_tail n 3 ≠ 0 := by
    rw [ha3]
    intro h_zero
    have h_zero_num : Q_explicit n 2 = 0 := (div_eq_zero_iff.mp h_zero).resolve_right (by exact_mod_cast hq3_nz)
    exact hq2_nz h_zero_num
  have hval_nz : 2 - 3 / continued_fraction_tail n 3 ≠ 0 := by
    intro h_zero
    have h_eq : 1 / (2 - 3 / continued_fraction_tail n 3) = 0 := by rw [h_zero, div_zero]
    rw [haux] at h_eq
    have h_zero_num : Q_explicit n 2 = 0 := (div_eq_zero_iff.mp h_eq).resolve_right (by exact_mod_cast hq1_nz)
    exact hq2_nz h_zero_num
  have hunfold := val_eq_unfold n hn ha3_nz hval_nz
  rw [hunfold]
  exact haux

lemma a_val_aux (n : ℕ) (hn : n ≥ 4)
  (hval : continued_fraction_val n = Q_explicit n 2 / Q_explicit n 1)
  (hq1 : Q_explicit n 1 = 5 * (n : ℚ) - 4)
  (hq2 : Q_explicit n 2 = (IntQ2 n : ℚ) / 2) :
  continued_fraction_val n = (IntQ2 n : ℚ) / (2 * (5 * (n : ℤ) - 4) : ℤ) := by
  zify [div_div, true, *]

lemma a_val (n : ℕ) (hn : n ≥ 4) :
  a n = ((IntQ2 n : ℚ) / ((2 * (5 * (n : ℤ) - 4) : ℤ) : ℚ)).den := by
  have h_val := val_eq n hn
  have hq1 : Q_explicit n 1 = 5 * (n : ℚ) - 4 := rfl
  have hq2 : Q_explicit n 2 = (IntQ2 n : ℚ) / 2 := Q2_eq n
  have haux := a_val_aux n hn h_val hq1 hq2
  have han : a n = (continued_fraction_val n).den := by
    rw [a]
    have hlt : ¬ (n < 3) := by omega
    simp [hlt]
  rw [han, haux]

lemma rat_den_divides (num den : ℤ) (hden : den ≠ 0) : ((num : ℚ) / (den : ℚ)).den ∣ den.natAbs := by
  exact (mod_cast@den.natCast_dvd.1 (Rat.den_dvd _ _))

lemma a_eq_p_implies_p_divides (n p : ℕ) (hn : n ≥ 3) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hap : a n = p) :
  (p : ℤ) ∣ (5 * (n : ℤ) - 4) := by
  obtain h_eq | h_gt := eq_or_lt_of_le hn
  · subst h_eq
    simp_all[a, false,comm]
    norm_num[continued_fraction_val]
  · have hn4 : n ≥ 4 := h_gt
    have ha := a_val n hn4
    have h_den_nz : 2 * (5 * (n : ℤ) - 4) ≠ 0 := by
      omega
    have h_div : ((IntQ2 n : ℚ) / ((2 * (5 * (n : ℤ) - 4) : ℤ) : ℚ)).den ∣ (2 * (5 * (n : ℤ) - 4)).natAbs := rat_den_divides (IntQ2 n) (2 * (5 * (n : ℤ) - 4)) h_den_nz
    rw [← ha, hap] at h_div
    exact (Int.natCast_dvd.mpr (( (p.coprime_primes hp (by decide)).mpr hp2).dvd_mul_left.mp (h_div.trans (Int.natAbs_mul _ _).dvd)))

lemma intQ2_mod_p (n p k : ℕ) (hn : n ≥ 3) (hp : 5 * n - 4 = k * p) :
  ∃ m : ℤ, IntQ2 n = m * p + ((n : ℤ) - 1) * (n - 3).factorial * ((n : ℤ) + 4) := by
  push_cast[IntQ2,←sub_eq_iff_eq_add,←dvd_iff_exists_eq_mul_left,←Int.ofNat_inj,(mul_right_mono hn).trans']at*
  exact (dvd_of_mul_left_dvd ⟨ _,by rw [ hp,add_sub_cancel_right]⟩)

lemma p_dvd_intQ2_of_ge (n p : ℕ) (hn : n ≥ p + 3) (hp : Nat.Prime p) (hd : (p : ℤ) ∣ 5 * n - 4) :
  (p : ℤ) ∣ IntQ2 n := by
  delta IntQ2
  apply (hd.mul_right _).add (.mul_right ↑(.mul_left ↑(mod_cast hp.dvd_factorial.mpr (p.le_sub_of_add_le (↑hn))) _) _)

lemma p_sq_dvd (n p : ℕ) (hn : n ≥ 4) (hp : Nat.Prime p) (hap : a n = p)
  (hdvd : (p : ℤ) ∣ IntQ2 n) :
  p ^ 2 ∣ 2 * (5 * n - 4) := by
  have ha := a_val n hn
  rw [hap] at ha
  set D : ℤ := 2 * (5 * (n : ℤ) - 4)
  have hD_pos : D > 0 := by omega
  have hD_nz : (D : ℚ) ≠ 0 := by exact_mod_cast hD_pos.ne.symm
  set q : ℚ := (IntQ2 n : ℚ) / (D : ℚ)
  have hden : q.den = p := ha.symm
  have hq_mul : q * (D : ℚ) = (IntQ2 n : ℚ) := by
    have h2 : q = (IntQ2 n : ℚ) / (D : ℚ) := rfl
    rw [h2]
    exact div_mul_cancel₀ _ hD_nz
  have h_cross_rat : (q.num : ℚ) * (D : ℚ) = (IntQ2 n : ℚ) * (q.den : ℚ) := by
    have h1 : (q.num : ℚ) / (q.den : ℚ) = q := Rat.num_div_den q
    have h_sub : ((q.num : ℚ) / (q.den : ℚ)) * (D : ℚ) = (IntQ2 n : ℚ) := by
      rw [h1, hq_mul]
    have hden_nz : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_pos.ne.symm
    calc (q.num : ℚ) * (D : ℚ)
      _ = ((q.num : ℚ) / (q.den : ℚ) * (q.den : ℚ)) * (D : ℚ) := by rw [div_mul_cancel₀ _ hden_nz]
      _ = ((q.num : ℚ) / (q.den : ℚ) * (D : ℚ)) * (q.den : ℚ) := by ring
      _ = (IntQ2 n : ℚ) * (q.den : ℚ) := by rw [h_sub]
  have h_cross : q.num * D = IntQ2 n * q.den := by exact_mod_cast h_cross_rat
  have h_p_div_N_den_nat : p ^ 2 ∣ (IntQ2 n).natAbs * q.den := by
    have h1 : (p : ℤ) ∣ IntQ2 n := hdvd
    have h2 : p ∣ (IntQ2 n).natAbs := Int.natAbs_dvd_natAbs.mpr h1
    have h3 : p ^ 2 = p * p := by ring
    rw [h3, hden]
    exact mul_dvd_mul h2 (dvd_refl p)
  have h_cross_nat : q.num.natAbs * D.natAbs = (IntQ2 n).natAbs * q.den := by
    have h1 := congrArg Int.natAbs h_cross
    have h2 : (q.num * D).natAbs = q.num.natAbs * D.natAbs := Int.natAbs_mul q.num D
    have h3 : (IntQ2 n * (q.den : ℤ)).natAbs = (IntQ2 n).natAbs * q.den := by
      have h3_1 : (IntQ2 n * (q.den : ℤ)).natAbs = (IntQ2 n).natAbs * (q.den : ℤ).natAbs := Int.natAbs_mul (IntQ2 n) (q.den : ℤ)
      have h3_2 : (q.den : ℤ).natAbs = q.den := rfl
      rw [h3_2] at h3_1
      exact h3_1
    rw [h2, h3] at h1
    exact h1
  rw [← h_cross_nat] at h_p_div_N_den_nat
  have h_coprime : q.num.natAbs.Coprime q.den := by
    have hc := Rat.reduced q
    exact hc
  have h_p_coprime : p.Coprime q.num.natAbs := by
    have h1 : q.num.natAbs.Coprime p := by
      rw [← hden]
      exact h_coprime
    exact h1.symm
  have h_p2_coprime : (p ^ 2).Coprime q.num.natAbs := Nat.Coprime.pow_left 2 h_p_coprime
  have h_p2_dvd_D_nat : p ^ 2 ∣ D.natAbs := by
    have h_comm : q.num.natAbs * D.natAbs = D.natAbs * q.num.natAbs := by ring
    rw [h_comm] at h_p_div_N_den_nat
    exact h_p2_coprime.dvd_of_dvd_mul_right h_p_div_N_den_nat
  have hD_nat : D.natAbs = 2 * (5 * n - 4) := by omega
  rw [hD_nat] at h_p2_dvd_D_nat
  exact_mod_cast h_p2_dvd_D_nat

lemma p_ge_7 (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) : p ≥ 7 := by
  match p with|0| (1)|4 | (6) =>contradiction | S+7 =>omega

lemma cross_mul_eq (n p : ℕ) (hn : n ≥ 4) (hap : a n = p) :
  ∃ q_num : ℤ, q_num * 2 * (5 * (n : ℤ) - 4) = IntQ2 n * p ∧ q_num.natAbs.Coprime p := by
  have ha := a_val n hn
  rw [hap] at ha
  set D : ℤ := 2 * (5 * (n : ℤ) - 4)
  have hD_pos : D > 0 := by omega
  have hD_nz : (D : ℚ) ≠ 0 := by exact_mod_cast hD_pos.ne.symm
  set q : ℚ := (IntQ2 n : ℚ) / (D : ℚ)
  have hden : q.den = p := ha.symm
  have hq_mul : q * (D : ℚ) = (IntQ2 n : ℚ) := by
    have h2 : q = (IntQ2 n : ℚ) / (D : ℚ) := rfl
    rw [h2]
    exact div_mul_cancel₀ _ hD_nz
  have h_cross_rat : (q.num : ℚ) * (D : ℚ) = (IntQ2 n : ℚ) * (q.den : ℚ) := by
    have h1 : (q.num : ℚ) / (q.den : ℚ) = q := Rat.num_div_den q
    have h_sub : ((q.num : ℚ) / (q.den : ℚ)) * (D : ℚ) = (IntQ2 n : ℚ) := by
      rw [h1, hq_mul]
    have hden_nz : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_pos.ne.symm
    calc (q.num : ℚ) * (D : ℚ)
      _ = ((q.num : ℚ) / (q.den : ℚ) * (q.den : ℚ)) * (D : ℚ) := by rw [div_mul_cancel₀ _ hden_nz]
      _ = ((q.num : ℚ) / (q.den : ℚ) * (D : ℚ)) * (q.den : ℚ) := by ring
      _ = (IntQ2 n : ℚ) * (q.den : ℚ) := by rw [h_sub]
  have h_cross : q.num * D = IntQ2 n * q.den := by exact_mod_cast h_cross_rat
  use q.num
  constructor
  · have h1 : q.num * 2 * (5 * (n : ℤ) - 4) = q.num * D := by ring
    rw [h1]
    have h2 : IntQ2 n * p = IntQ2 n * q.den := by rw [hden]
    rw [h2]
    exact h_cross
  · have hc := Rat.reduced q
    rw [hden] at hc
    exact hc

lemma p_sq_dvd_5n_4 (n p : ℕ) (hn : n ≥ 4) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hap : a n = p) (h_ge : n ≥ p + 3) :
  (p ^ 2 : ℤ) ∣ 5 * (n : ℤ) - 4 := by
  have hdvd : (p : ℤ) ∣ 5 * (n : ℤ) - 4 := a_eq_p_implies_p_divides n p (by omega) hp hp2 hap
  have hdvd_intQ2 : (p : ℤ) ∣ IntQ2 n := p_dvd_intQ2_of_ge n p h_ge hp hdvd
  have h_cross := cross_mul_eq n p hn hap
  rcases h_cross with ⟨q_num, h_eq, h_coprime⟩
  have h_pk_dvd_rhs : (p ^ 2 : ℤ) ∣ IntQ2 n * p := by
    have h1 : (p ^ 2 : ℤ) = (p : ℤ) * (p : ℤ) := by ring
    rw [h1]
    exact mul_dvd_mul hdvd_intQ2 (dvd_refl (p : ℤ))
  have h_pk_dvd_lhs : (p ^ 2 : ℤ) ∣ q_num * 2 * (5 * (n : ℤ) - 4) := by
    rw [h_eq]
    exact h_pk_dvd_rhs
  have h_coprime_p : p.Coprime q_num.natAbs := h_coprime.symm
  have h_coprime_pk : (p ^ 2).Coprime q_num.natAbs := Nat.Coprime.pow_left 2 h_coprime_p
  have h_coprime_2 : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr (by
    intro h
    have h_eq2 : p = 2 := by
      cases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two p h with
      | inl h1 =>
        have h_p1 : p > 1 := hp.one_lt
        omega
      | inr h2 => exact h2
    exact hp2 h_eq2)
  have h_coprime_pk2 : (p ^ 2).Coprime 2 := Nat.Coprime.pow_left 2 h_coprime_2
  have h_coprime_mul : (p ^ 2).Coprime (q_num.natAbs * 2) := Nat.Coprime.mul_right h_coprime_pk h_coprime_pk2
  have h_lhs_nat : (q_num * 2 * (5 * (n : ℤ) - 4)).natAbs = q_num.natAbs * 2 * (5 * n - 4) := by
    have h1 : (q_num * 2 * (5 * (n : ℤ) - 4)).natAbs = (q_num * 2).natAbs * (5 * (n : ℤ) - 4).natAbs := Int.natAbs_mul (q_num * 2) (5 * (n : ℤ) - 4)
    have h2 : (q_num * 2).natAbs = q_num.natAbs * (2 : ℤ).natAbs := Int.natAbs_mul q_num 2
    have h3 : (5 * (n : ℤ) - 4).natAbs = 5 * n - 4 := by omega
    have h2b : (2 : ℤ).natAbs = 2 := rfl
    rw [h2b] at h2
    rw [h1, h2, h3]
  have h_dvd_nat : p ^ 2 ∣ (q_num * 2 * (5 * (n : ℤ) - 4)).natAbs := Int.natAbs_dvd_natAbs.mpr h_pk_dvd_lhs
  rw [h_lhs_nat] at h_dvd_nat
  have h_final_nat : p ^ 2 ∣ 5 * n - 4 := h_coprime_mul.dvd_of_dvd_mul_left h_dvd_nat
  have h_int_dvd : (p ^ 2 : ℤ) ∣ (5 * n - 4 : ℕ) := by exact_mod_cast h_final_nat
  have h_eq_5n : ((5 * n - 4 : ℕ) : ℤ) = 5 * (n : ℤ) - 4 := by omega
  rw [← h_eq_5n]
  exact h_int_dvd

lemma p_pow_dvd_intQ2 (n p k : ℕ) (hn : n ≥ 4) (hp : p ≥ 7) (h_prime : Nat.Prime p) (hk : k ≥ 2)
  (hdvd_5n : (p ^ k : ℤ) ∣ 5 * (n : ℤ) - 4) : (p ^ k : ℤ) ∣ IntQ2 n := by
  rw [←mul_comm,IntQ2] at*
  refine .add (.mul_right (by rwa[mul_comm]) _) ↑((((dvd_trans) ?_ (Int.ofNat_dvd.2 (Nat.factorial_mul_factorial_dvd_factorial (p.le_sub_of_add_le ?_)))).mul_left _).mul_right _)
  · rcases k with a | S | S | S | S
    · tauto
    · contradiction
    · refine mod_cast match p with | S+1 =>sq (S + 1)▸mul_dvd_mul ⟨_, rfl⟩ (h_prime.dvd_factorial.mpr (S.succ.le_sub_of_add_le ((Nat.le_sub_of_add_le) ? _) ) )
      obtain ⟨rfl⟩ :=eq_or_ne S @6
      · use not_lt.mp fun and=>absurd hdvd_5n (by valid : ¬49 ∣(_ : ℤ))
      obtain ⟨@c⟩ :=eq_or_ne S 8
      · trivial
      obtain ⟨rfl⟩ :=eq_or_ne S 10
      · cases show(121 : ℤ) ∣ _ by valid with omega
      obtain ⟨rfl⟩ :=eq_or_ne S 12
      · cases show(169: Int) ∣ _ by valid with omega
      · linarith only[sq_nonneg (S-13 : ℤ),Int.le_of_dvd (by valid) ( show(S+1 : ℤ)^2 ∣ _ from hdvd_5n), (by cases h_prime.eq_two_or_odd with valid: S≥14)]
    · refine mod_cast pow_three p▸mul_dvd_mul (p.dvd_factorial h_prime.pos (by constructor)) (Nat.dvd_factorial (by positivity) (Nat.le_sub_of_add_le (Nat.le_sub_of_add_le @?_)))
      nlinarith only[Int.le_of_dvd (by valid) (pow_succ (p : ℤ) (2)▸(‹_›:)),hp]
    · refine mod_cast ((h_prime.pow_dvd_iff_le_factorization (by positivity)).2.comp (Nat.factorization_def _ (by valid)).ge.trans' ?_).mul_left _
      refine (by_contra ↑(absurd (Fact.mk @h_prime) fun and=>. (.trans (? _) (padicValNat_factorial (@Nat.le_succ ↑_)).ge)))
      simp_all-contextual [pow_add,n.sub_sub, Finset.sum_Ico_eq_sum_range _,Nat.succ_sub_one _, Finset.sum_range_succ']
      use le_add_self.trans_lt' ((p.le_div_iff_mul_le h_prime.pos).2<|Nat.le_sub_of_add_le ?_)
      nlinarith only [hp, mul_le_mul_left' hp (p^S), mul_le_mul_left' hp (p^2),Int.le_of_dvd (by valid) hdvd_5n, S.lt_pow_self h_prime.one_lt]
  · linarith only[hp, mul_le_mul_left' hp p,Int.le_of_dvd (by valid) (.trans (pow_dvd_pow _ hk) (by valid:))]

lemma p_pow_dvd_5n_4_step (n p k : ℕ) (hn : n ≥ 4) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hap : a n = p)
  (hk : k ≥ 2) (ih : (p ^ k : ℤ) ∣ 5 * (n : ℤ) - 4) : (p ^ (k + 1) : ℤ) ∣ 5 * (n : ℤ) - 4 := by
  have hp7 : p ≥ 7 := p_ge_7 p hp hp2 hp3 hp5
  have hdvd_int : (p ^ k : ℤ) ∣ IntQ2 n := p_pow_dvd_intQ2 n p k hn hp7 hp hk ih
  have h_cross := cross_mul_eq n p hn hap
  rcases h_cross with ⟨q_num, h_eq, h_coprime⟩
  have h_pk_dvd_rhs : (p ^ (k + 1) : ℤ) ∣ IntQ2 n * p := by
    have h1 : (p ^ (k + 1) : ℤ) = (p ^ k : ℤ) * (p : ℤ) := by push_cast; ring
    rw [h1]
    exact mul_dvd_mul hdvd_int (dvd_refl (p : ℤ))
  have h_pk_dvd_lhs : (p ^ (k + 1) : ℤ) ∣ q_num * 2 * (5 * (n : ℤ) - 4) := by
    rw [h_eq]
    exact h_pk_dvd_rhs
  have h_coprime_p : p.Coprime q_num.natAbs := h_coprime.symm
  have h_coprime_pk : (p ^ (k + 1)).Coprime q_num.natAbs := Nat.Coprime.pow_left (k + 1) h_coprime_p
  have h_coprime_2 : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr (by
    intro h
    have h_eq2 : p = 2 := by
      cases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two p h with
      | inl h1 =>
        have h_p1 : p > 1 := hp.one_lt
        omega
      | inr h2 => exact h2
    exact hp2 h_eq2)
  have h_coprime_pk2 : (p ^ (k + 1)).Coprime 2 := Nat.Coprime.pow_left (k + 1) h_coprime_2
  have h_coprime_mul : (p ^ (k + 1)).Coprime (q_num.natAbs * 2) := Nat.Coprime.mul_right h_coprime_pk h_coprime_pk2
  have h_lhs_nat : (q_num * 2 * (5 * (n : ℤ) - 4)).natAbs = q_num.natAbs * 2 * (5 * n - 4) := by
    have h1 : (q_num * 2 * (5 * (n : ℤ) - 4)).natAbs = (q_num * 2).natAbs * (5 * (n : ℤ) - 4).natAbs := Int.natAbs_mul (q_num * 2) (5 * (n : ℤ) - 4)
    have h2 : (q_num * 2).natAbs = q_num.natAbs * (2 : ℤ).natAbs := Int.natAbs_mul q_num 2
    have h3 : (5 * (n : ℤ) - 4).natAbs = 5 * n - 4 := by omega
    have h2b : (2 : ℤ).natAbs = 2 := rfl
    rw [h2b] at h2
    rw [h1, h2, h3]
  have h_dvd_nat : p ^ (k + 1) ∣ (q_num * 2 * (5 * (n : ℤ) - 4)).natAbs := Int.natAbs_dvd_natAbs.mpr h_pk_dvd_lhs
  rw [h_lhs_nat] at h_dvd_nat
  have h_final_nat : p ^ (k + 1) ∣ 5 * n - 4 := h_coprime_mul.dvd_of_dvd_mul_left h_dvd_nat
  have h_int_dvd : (p ^ (k + 1) : ℤ) ∣ (5 * n - 4 : ℕ) := by exact_mod_cast h_final_nat
  have h_eq_5n : ((5 * n - 4 : ℕ) : ℤ) = 5 * (n : ℤ) - 4 := by omega
  rw [← h_eq_5n]
  exact h_int_dvd

lemma p_pow_dvd_all_shifted (n p : ℕ) (hn : n ≥ 4) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hap : a n = p) (h_ge : n ≥ p + 3) :
  ∀ d : ℕ, (p ^ (d + 2) : ℤ) ∣ 5 * (n : ℤ) - 4 := by
  intro d
  induction d with
  | zero =>
    have h : 0 + 2 = 2 := rfl
    rw [h]
    exact p_sq_dvd_5n_4 n p hn hp hp2 hap h_ge
  | succ d ih =>
    have h : d + 1 + 2 = d + 2 + 1 := by omega
    rw [h]
    have hk : d + 2 ≥ 2 := by omega
    exact p_pow_dvd_5n_4_step n p (d + 2) hn hp hp2 hp3 hp5 hap hk ih

lemma p_pow_gt (n p : ℕ) (hp : p ≥ 7) : (p ^ (5 * n) : ℤ) > 5 * (n : ℤ) - 4 := by
  refine(sub_lt_self _ (by constructor) ).trans (mod_cast((Nat.lt_pow_self (by valid))))

lemma a_eq_p_implies_n_lt (n p : ℕ) (hn : n ≥ 3) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hap : a n = p) :
  n < p + 3 := by
  by_contra h_ge
  push_neg at h_ge
  have hp_pos : p ≥ 2 := hp.two_le
  have hn4 : n ≥ 4 := by omega
  have h_pow_dvd : ∀ d : ℕ, (p ^ (d + 2) : ℤ) ∣ 5 * (n : ℤ) - 4 := p_pow_dvd_all_shifted n p hn4 hp hp2 hp3 hp5 hap h_ge
  have hp7 : p ≥ 7 := p_ge_7 p hp hp2 hp3 hp5
  have h_dvd_5n : (p ^ (5 * n) : ℤ) ∣ 5 * (n : ℤ) - 4 := by
    have h_eq : 5 * n = (5 * n - 2) + 2 := by omega
    rw [h_eq]
    exact h_pow_dvd (5 * n - 2)
  have h_gt : (p ^ (5 * n) : ℤ) > 5 * (n : ℤ) - 4 := p_pow_gt n p hp7
  have h_pos : 5 * (n : ℤ) - 4 > 0 := by omega
  have h_le : (p ^ (5 * n) : ℤ) ≤ 5 * (n : ℤ) - 4 := Int.le_of_dvd h_pos h_dvd_5n
  linarith

def g_p (p : ℕ) : ℕ :=
  if p % 5 = 1 then 1
  else if p % 5 = 2 then 3
  else if p % 5 = 3 then 2
  else if p % 5 = 4 then 4
  else 0

lemma g_p_prop (p : ℕ) (hprime : Nat.Prime p) (hp : p ≠ 5) (hodd : p % 2 = 1) :
  (g_p p * p) % 5 = 1 ∧ g_p p ∈ ({1, 2, 3, 4} : Set ℕ) := by
  delta g_p
  match H:p%5 with|0=>cases hp ((hprime.dvd_iff_eq (by decide)).1.comp (5).dvd_of_mod_eq_zero H)|1|2|3|4=>push_cast+decide[ H,Nat.mul_mod] | S+5=>omega

def n_p (p : ℕ) : ℕ := (g_p p * p + 4) / 5

lemma n_p_prop (p : ℕ) (hprime : Nat.Prime p) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hodd : p % 2 = 1) :
  5 * n_p p - 4 = g_p p * p ∧ n_p p ≥ 3 := by
  delta g_p n_p
  repeat' split
  · match hprime.one_lt with|m=>omega
  · omega
  · omega
  · omega
  · rcases hp5 ↑( (hprime.dvd_iff_eq ( (by decide))).mp (by valid))

lemma existence_intQ2_not_dvd (p : ℕ) (hp : Nat.Prime p) (hp2 : p % 2 = 1) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
  ¬ (p : ℤ) ∣ IntQ2 (n_p p) := by
  delta n_p IntQ2 Ne at*
  rw_mod_cast[ g_p]
  (repeat' split)
  · simp_all[p.add_div, add_eq_zero_iff_eq_neg',sum_fact,mul_assoc,←CharP.intCast_eq_zero_iff (ZMod p)]
    use fun and=>absurd (Fact.mk hp) fun and' =>mul_ne_zero (by match hp.one_lt with | S=>omega ∘p.eq_zero_of_dvd_of_lt ∘(CharP.cast_eq_zero_iff _ _ _).1) ?_ (and.trans (?_))
    · norm_num[CharP.cast_eq_zero_iff _ p,hp.dvd_factorial, (by valid:p/5-2<p)]
      norm_cast
      obtain ⟨@c⟩ :=eq_or_ne p 7
      · omega
      · use fun and=>absurd (p.le_of_dvd · ((CharP.cast_eq_zero_iff _ _ _).1 (mod_cast and))) (hp.ne_one ∘by valid)
    · norm_num[add_sub_assoc, mul_add,show (5 * ↑(p/5):ZMod p)=-1 from add_eq_zero_iff_eq_neg.1 (mod_cast _),‹_=1›▸p.div_add_mod 5]
  · simp_all[sum_fact, add_eq_zero_iff_eq_neg',←CharP.intCast_eq_zero_iff (ZMod p), (by valid:5*( (3*p+4)/5)=4+3*p)]
    have:=Fact.mk hp
    norm_num[*, sub_eq_zero, add_eq_zero_iff_eq_neg,CharP.cast_eq_zero_iff _ p,hp.dvd_factorial, (by valid: (3*p+4)/5≤ (3*p+4)/5)]
    use⟨? _,by valid⟩,?_
    · exact (mod_cast (by valid ∘ (ZMod.val_one p▸.▸ZMod.val_cast_of_lt)))
    by_cases h:(p:Int) ∣ (3*p+4)/5+4
    · match p with|7|9=>contradiction | S+10=>use (by valid ∘Int.le_of_dvd (by valid)) h
    · use fun and=>by simp_all[←CharP.intCast_eq_zero_iff (ZMod p)]
  · simp_all[sum_fact, add_eq_zero_iff_eq_neg,<-ZMod.intCast_zmod_eq_zero_iff_dvd, (by valid:5*( (2*p+4)/5)-4=2*p∧ 1 ≤ (2*p+4)/5)]
    have:=(2*p+4).mod_add_div 5
    simp_all[sum_fact,Nat.add_mod,Nat.mul_mod]
    use absurd (Fact.mk hp) ∘ fun and j=>mul_ne_zero (mul_ne_zero (sub_ne_zero.2 fun and=>? _) (by valid ∘hp.dvd_factorial.1.comp (CharP.cast_eq_zero_iff _ _ _).1)) ?_ (neg_eq_zero.1 (and.symm.trans (mod_cast by simp_all)))
    · use absurd (ZMod.val_one p▸and▸ZMod.val_cast_of_lt)<|by valid
    norm_cast
    exact (mod_cast(CharP.cast_eq_zero_iff _ _ _).not.2 (by match p with | S+15=>omega ∘Nat.eq_zero_of_dvd_of_lt))
  · norm_num[*,←CharP.intCast_eq_zero_iff (ZMod p),Nat.mul_div_cancel',(5).dvd_iff_mod_eq_zero,Nat.add_mod,Nat.mul_mod]
    use fun and=>absurd (Fact.mk hp) fun and' =>mul_ne_zero (mul_ne_zero (sub_ne_zero.2 fun and=>? _) (by valid ∘hp.dvd_factorial.1.comp (CharP.cast_eq_zero_iff _ _ _).1)) (mod_cast ?_) and
    · exact ( (ZMod.eq_iff_modEq_nat p).not.mpr ↑(mt ↑(·.eq_of_abs_lt ∘max_lt_iff.mpr) (by valid))) (and.trans Nat.cast_one.symm)
    · exact (CharP.cast_eq_zero_iff _ _ _).not.2 (·.elim (by match. with|0|1=>use fun and=> (by match p with | S+15=>omega) | n+2=>use p.mul_add _ _▸by valid))
  · use absurd (hp.eq_one_or_self_of_dvd 5) (by valid)

lemma a_3_eq_11 : a 3 = 11 := by
  rw [←eq_comm, a]
  norm_num[continued_fraction_val]

lemma n_p_ge_4 (p : ℕ) (hp : Nat.Prime p) (hp2 : p % 2 = 1) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp11 : p ≠ 11) :
  n_p p ≥ 4 := by
  simp_rw [(n_p ·),Nat.succ_le]
  push_cast [ Ne,Nat.lt_div_iff_mul_lt,g_p]at *
  match p with|1|7|9|11|13|15=>trivial | S+17=>exact (Nat.le_mul_of_pos_left _ (pos_of_ne_zero (absurd (hp.eq_one_or_self_of_dvd 5) ∘by grind))).trans' (by valid)

lemma p_mod_5_cases (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≠ 5) :
  p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
  have hp_mod_0 : p % 5 ≠ 0 := by
    intro h
    have h_dvd : 5 ∣ p := Nat.dvd_of_mod_eq_zero h
    have h_eq5 : p = 5 := by
      cases Nat.Prime.eq_one_or_self_of_dvd hp 5 h_dvd with
      | inl h1 =>
        have h_p1 : p > 1 := hp.one_lt
        omega
      | inr h5 => exact h5.symm
    exact hp5 h_eq5
  omega

lemma two_g_p_dvd_intQ2 (p : ℕ) (hp : Nat.Prime p) (hp2 : p % 2 = 1) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp11 : p ≠ 11) :
  (2 * g_p p : ℤ) ∣ IntQ2 (n_p p) := by
  have hp_mod := p_mod_5_cases p hp hp5
  rcases hp_mod with h1 | h2 | h3 | h4
  · simp_all[IntQ2,n_p, true,g_p]
    delta sum_fact
    refine .add ?_ (Int.prime_two.dvd_mul.2 (or_iff_not_imp_right.2 fun and=>.mul_right (by valid) (_)))
    exact (.mul_left ↑(mod_cast(2).le_induction (by decide) ( fun and R L=>L.add ((2).factorial_dvd_factorial (by push_cast[R.trans']))) ( _) (by match hp.one_lt with | S=>omega:_-3≥2)) _)
  · simp_all![IntQ2,g_p,n_p]
    rw [←p.mod_add_div,h2]at hp2⊢
    simp_all![add_sub_right_comm, mul_add, add_right_comm,mul_left_comm (3 : ℤ),Int.add_mul_ediv_left]
    ring
    replace hp3:(sum_fact ((10+p/5*15)/5-3): Int) % 2 =0
    · simp_all![add_comm 2,Nat.add_mod,Nat.add_div,Nat.mul_mod,Nat.mul_div_assoc _, Finset.sum_int_mod]
      delta sum_fact
      exact (mod_cast(2).le_induction (by decide) ( fun and A B=>B.add ((2).factorial_dvd_factorial A)) ( _) (by valid:_-1≥2))
    · cases(Int.dvd_of_emod_eq_zero hp3).mul_left (p/5)
      cases(Int.dvd_of_emod_eq_zero hp3).mul_right ((10+p/5*15)/5-3)!
      cases Even.two_dvd (by norm_num[parity_simps] :Even ((p/5 : ℤ)^2*( (10+p/5*15)/5-3)!+(p/5) * ( (10+p/5*15)/5-3)!)) with valid
  · simp_all![IntQ2, g_p, false, n_p]
    obtain ⟨a, _⟩|⟨C, _⟩ := ( (2*p+4 : ℤ)/5-3).even_or_odd
    · omega
    obtain ⟨a, rfl⟩| ⟨a, rfl⟩:= C.even_or_odd
    · match p with | S+7=>omega
    norm_num[sum_fact, mul_add, add_assoc,eq_add_of_sub_eq (by valid),←mul_assoc]
    norm_num[sum_fact, mul_add, add_assoc, (by valid: (2*p+4)/5-3=2*(2*a+1).toNat+1),←mul_assoc]
    ring
    delta sum_fact
    cases(2).dvd_factorial two_pos (by valid:(1+a*2).toNat*2≥2)
    simp_all![add_comm (1 : ℕ),mul_assoc]
    ring
    revert‹ℕ›a hp hp2 hp3 hp5 hp11 h3
    use fun and _ _ _ _ A B _ _ _=>.add (.add (.add ?_ ? _) (by valid)) (by valid)
    · match p with|1|7 | S+9=>omega
    · exact (mod_cast mul_dvd_mul ((2).dvd_trans (by decide) (by exact(2).le_induction (by decide) ( fun and a s=>s.add ((2).factorial_dvd_factorial a)) _ (by valid:_*2 > 1): (2 ∣ _) ) ) (by decide:2 ∣26))
  · simp_all [IntQ2, g_p, false,n_p]
    convert(dvd_add _ _)
    · infer_instance
    · delta sum_fact
      exact (.trans (by decide) (mul_dvd_mul (by valid: (4: Int) ∣ _) (show (2 ∣ _) from mod_cast(3).le_induction (by decide) ( fun and A B=>B.add ((2).factorial_dvd_factorial (by valid))) _ (by valid:_/5-3≥3))))
    · apply((dvd_trans (by decide) (Nat.factorial_dvd_factorial (by·omega:_≥4)).natCast).mul_left @_).mul_right

lemma a_n_p_eq_p_of_ne_11 (p : ℕ) (hp : Nat.Prime p) (hp2 : p % 2 = 1) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp11 : p ≠ 11) :
  a (n_p p) = p := by
  have hn4 : n_p p ≥ 4 := n_p_ge_4 p hp hp2 hp3 hp5 hp11
  have ha := a_val (n_p p) hn4
  have h_np_prop := n_p_prop p hp hp3 hp5 hp2
  have h_5n : 5 * n_p p - 4 = g_p p * p := h_np_prop.1
  have h_5n_int : 5 * (n_p p : ℤ) - 4 = g_p p * p := by
    have h_eq : 5 * (n_p p : ℤ) - 4 = ((5 * n_p p - 4 : ℕ) : ℤ) := by omega
    rw [h_eq, h_5n]
    push_cast
    rfl
  have h_den : (2 * (5 * (n_p p : ℤ) - 4) : ℤ) = 2 * g_p p * p := by
    calc (2 * (5 * (n_p p : ℤ) - 4) : ℤ) = 2 * (g_p p * p : ℤ) := by rw [h_5n_int]
      _ = 2 * g_p p * p := by ring
  rw [h_den] at ha
  have hdvd : (2 * g_p p : ℤ) ∣ IntQ2 (n_p p) := two_g_p_dvd_intQ2 p hp hp2 hp3 hp5 hp11
  rcases hdvd with ⟨m, hm⟩
  have h_frac : (IntQ2 (n_p p) : ℚ) / ((2 * g_p p * p : ℤ) : ℚ) = (m : ℚ) / (p : ℚ) := by
    have h1 : (IntQ2 (n_p p) : ℚ) = (2 * g_p p : ℚ) * (m : ℚ) := by
      have hm_q : (IntQ2 (n_p p) : ℚ) = ((2 * g_p p * m : ℤ) : ℚ) := by rw [← hm]
      push_cast at hm_q
      exact hm_q
    have h2 : ((2 * g_p p * p : ℤ) : ℚ) = (2 * g_p p : ℚ) * (p : ℚ) := by push_cast; ring
    rw [h1, h2]
    have h_gp_pos : g_p p > 0 := by
      have hgp := g_p_prop p hp hp5 (by omega)
      rcases hgp.2 with h | h | h | h <;> (rw [h]; norm_num)
    have h_nz : (2 * g_p p : ℚ) ≠ 0 := by exact_mod_cast (by omega : 2 * g_p p > 0).ne.symm
    exact mul_div_mul_left (m : ℚ) (p : ℚ) h_nz
  rw [h_frac] at ha
  have h_not_dvd : ¬ (p : ℤ) ∣ m := by
    intro h
    have h_int_dvd : (p : ℤ) ∣ IntQ2 (n_p p) := by
      rw [hm]
      have h_comm : (2 * g_p p : ℤ) * m = m * (2 * g_p p) := by ring
      rw [h_comm]
      exact dvd_mul_of_dvd_left h (2 * g_p p)
    have h_exist := existence_intQ2_not_dvd p hp hp2 hp3 hp5
    exact h_exist h_int_dvd
  have h_den_eq : ((m : ℚ) / (p : ℚ)).den = p := by
    refine Nat.cast_injective (Rat.den_div_eq_of_coprime (mod_cast hp.pos) (hp.coprime_iff_not_dvd.mpr (by assumption ∘m.natCast_dvd.mpr)).symm)
  rw [h_den_eq] at ha
  exact ha

lemma uniqueness_part (p : ℕ) (hp : Nat.Prime p) (hp2 : p % 2 = 1) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
  (n1 n2 : ℕ) (hn1 : n1 ≥ 3) (hn2 : n2 ≥ 3)
  (h1 : a n1 = p) (h2 : a n2 = p) : n1 = n2 := by
  have hp_odd : p ≠ 2 := by
    rintro rfl; norm_num at hp2
  have hd1 : (p : ℤ) ∣ (5 * (n1 : ℤ) - 4) := a_eq_p_implies_p_divides n1 p hn1 hp hp_odd h1
  have hd2 : (p : ℤ) ∣ (5 * (n2 : ℤ) - 4) := a_eq_p_implies_p_divides n2 p hn2 hp hp_odd h2
  have hd3 : (p : ℤ) ∣ (5 * (n1 : ℤ) - 4) - (5 * (n2 : ℤ) - 4) := dvd_sub hd1 hd2
  have hd4 : (p : ℤ) ∣ 5 * ((n1 : ℤ) - (n2 : ℤ)) := by
    have h_eq : (5 * (n1 : ℤ) - 4) - (5 * (n2 : ℤ) - 4) = 5 * ((n1 : ℤ) - (n2 : ℤ)) := by ring
    rwa [h_eq] at hd3
  have hd5 : (p : ℤ) ∣ ((n1 : ℤ) - (n2 : ℤ)) := by
    exact ( (p.coprime_primes hp (by decide)).2 hp5).cast.dvd_of_dvd_mul_left hd4
  have hlt1 : n1 < p + 3 := a_eq_p_implies_n_lt n1 p hn1 hp hp_odd hp3 hp5 h1
  have hlt2 : n2 < p + 3 := a_eq_p_implies_n_lt n2 p hn2 hp hp_odd hp3 hp5 h2
  use (by valid ∘p.eq_zero_of_dvd_of_lt) (Int.natCast_dvd.1 hd5)

lemma existence_part (p : ℕ) (hp : Nat.Prime p) (hp2 : p % 2 = 1) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
  ∃ n, n ≥ 3 ∧ a n = p := by
  by_cases hp11 : p = 11
  · use 3
    refine ⟨by norm_num, ?_⟩
    subst hp11
    exact a_3_eq_11
  · use n_p p
    have h_np := n_p_prop p hp hp3 hp5 hp2
    refine ⟨h_np.2, ?_⟩
    exact a_n_p_eq_p_of_ne_11 p hp hp2 hp3 hp5 hp11
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : ∀ p : ℕ, Nat.Prime p ∧ p % 2 = 1 ∧ p ≠ 3 ∧ p ≠ 5 → ∃! n, n ≥ 3 ∧ a n = p := by
  -- EVOLVE-BLOCK-START
  rintro p ⟨hp, hp2, hp3, hp5⟩
  have hex : ∃ n, n ≥ 3 ∧ a n = p := existence_part p hp hp2 hp3 hp5
  rcases hex with ⟨n, hn3, hnp⟩
  use n
  refine ⟨⟨hn3, hnp⟩, ?_⟩
  rintro n2 ⟨hn2_3, hn2_p⟩
  exact uniqueness_part p hp hp2 hp3 hp5 n2 n hn2_3 hn3 hn2_p hnp
  -- EVOLVE-BLOCK-END
