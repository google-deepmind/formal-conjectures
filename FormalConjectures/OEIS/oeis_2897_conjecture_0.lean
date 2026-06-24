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




open Nat MvPolynomial

/--
The sequence $a(n)$ is defined by $a(n) = \binom{2n}{n}^3$.
We use `Nat.choose (2 * n) n` for the central binomial coefficient.
-/
def a (n : ℕ) : ℕ := (Nat.choose (2 * n) n) ^ 3

abbrev Vars := Fin 3

/--
The finsupp corresponding to the monomial $x^n y^n z^n$.
This is the map $\lambda i. n$. Since `Fin 3` is finite, this function is finitely supported.
We mark it noncomputable as it builds a mathematical object defined in terms of finite support.
-/
noncomputable def xyz_pow_n (n : ℕ) : Finsupp Vars ℕ :=
  Finsupp.ofSupportFinite (fun _ : Vars => n) (Set.toFinite _)

local notation "P" => MvPolynomial Vars ℤ

/--
The polynomial $P_n(X, Y, Z) = (1 + X + Y + Z)^{2n} (1 + X + Y - Z)^n (1 + X - Y + Z)^n$.
We identify $X_0, X_1, X_2$ with $X, Y, Z$.
We mark it noncomputable due to dependencies in the polynomial ring structure.
-/
noncomputable def P_n (n : ℕ) : P :=
  let X := MvPolynomial.X 0
  let Y := MvPolynomial.X 1
  let Z := MvPolynomial.X 2
  let p1 : P := 1 + X + Y + Z
  let p2 : P := 1 + X + Y - Z
  let p3 : P := 1 + X - Y + Z
  p1 ^ (2 * n) * p2 ^ n * p3 ^ n

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
noncomputable def yz_pow_n (n : ℕ) : Finsupp Vars ℕ :=
  Finsupp.update (xyz_pow_n n) 0 0

lemma combin_id (n j v : ℕ) (hv : v ≤ 2 * j) (hvn : v ≤ n) :
  (Nat.choose (2 * n) (2 * j) * Nat.choose (2 * n - 2 * j) (n - v) * Nat.choose (2 * j) v : ℤ) =
  (Nat.choose (2 * n) n * Nat.choose n v * Nat.choose n (2 * j - v) : ℤ) := by
  refine mod_cast if a:2*j≤2*n then if I:2*j-v≤n then(? _)else(? _)else if I:2*j-v≤n then(? _)else(? _)
  · simp_all only[mul_right_comm, two_mul,le_add_self,n.add_sub_assoc,←n.choose_symm_add,Nat.choose_mul]
    simp_all only[mul_assoc,mul_comm (n.choose _),←Nat.choose_symm (n.sub_le_sub_right _ _),le_self_add,n.add_sub_assoc,n.add_sub_cancel_left,Nat.sub_sub_sub_cancel_right,Nat.choose_mul]
    rwa[←n.add_sub_assoc hvn,Nat.sub_sub_sub_cancel_right]
  · simp_all only[mul_zero,zero_mul, (by valid:2*n-2*j<n-v),Nat.choose_eq_zero_of_lt, not_le]
  · omega
  · simp_all only[zero_mul,mul_zero, not_le,Nat.choose_eq_zero_of_lt]

lemma inner_sum_poly (n j : ℕ) :
  ∑ v ∈ Finset.range (2 * j + 1), (Nat.choose n v * Nat.choose n (2 * j - v) : ℤ) * (-1 : ℤ)^v =
  Polynomial.coeff ((1 - Polynomial.X : Polynomial ℤ)^n * (1 + Polynomial.X)^n) (2 * j) := by
  simp_rw [mul_assoc, sub_eq_neg_add (1: Polynomial Int), Polynomial.coeff_mul,Polynomial.coeff_one_add_X_pow]
  norm_num[add_pow,mul_comm ((-1)^ _),Finset.Nat.antidiagonal_eq_map,mul_assoc]
  refine Finset.sum_congr rfl fun R L=>symm<|.trans (by rw [ Finset.sum_eq_single R (by cases·.even_or_odd with simp_all[ Odd.neg_pow,comm])<|by simp_all[n.succ_le,n.choose_eq_zero_of_lt]]) ?_
  cases R.even_or_odd with·simp_all [ Odd.neg_pow]

lemma inner_sum_eq (n j : ℕ) :
  ∑ v ∈ Finset.Icc 0 (min n (2 * j)), (Nat.choose n v * Nat.choose n (2 * j - v) : ℤ) * (-1 : ℤ)^v =
  (Nat.choose n j : ℤ) * (-1 : ℤ)^j := by
  trans∑ a ∈.range (2 * j +1),(n).choose a*n.choose (2 * j-a) *(-1) ^ a
  · exact (Nat.range_succ_eq_Icc_zero _)▸ Finset.sum_subset (by bound) (by simp_all[n.choose_eq_zero_of_lt])
  refine mod_cast j.rec ↑( fun and=>.trans (add_zero _) ↑(by simp_all)) ( fun and I I=>.trans (by rw [Nat.mul_succ _, Finset.sum_range_succ _, Finset.sum_range_succ']) @? _) n
  induction I with |zero=>norm_num |succ=>_
  push_cast+contextual[Nat.succ_sub (Finset.mem_range.1 _), Finset.sum_add_distrib, mul_add, add_mul,Nat.sub_self,Nat.choose,pow_succ]at*
  rw [← (by valid:), Finset.sum_congr ↑rfl fun and (M) =>by rw [mul_neg_one, mul_neg], Finset.sum_neg_distrib, I, mul_neg_one, mul_neg, add_assoc _, Finset.sum_range_succ _, Finset.sum_range_succ']
  simp_all only[Nat.cast_one, mul_neg_one, mul_neg, add_assoc, one_mul, Finset.sum_neg_distrib,Nat.sub_self,Nat.sub_add_eq,Nat.succ_le,Nat.sub_zero,Nat.choose_self,mul_one,Nat.choose_zero_right,neg_neg,pow_succ]
  exact (by valid▸.trans (by rw [ Finset.sum_congr rfl fun and x =>(congr_arg₂ _) ((congr_arg _) ((congr_arg _) ((congr_arg _) ↑(Nat.sub_add_cancel (and.sub_pos_of_lt (List.mem_range.1 x)))))) rfl]) (by ring))

lemma sum_eq_step1 (n : ℕ) :
  (∑ j ∈ Finset.range (n + 1), ∑ v ∈ Finset.Icc 0 (min n (2 * j)),
    (Nat.choose (2 * n) (2 * j) * Nat.choose n j * Nat.choose (2 * n - 2 * j) (n - v) * Nat.choose (2 * j) v : ℤ) * (-1 : ℤ)^(j + v)) =
  (∑ j ∈ Finset.range (n + 1), ∑ v ∈ Finset.Icc 0 (min n (2 * j)),
    (Nat.choose (2 * n) n * Nat.choose n v * Nat.choose n (2 * j - v) : ℤ) * Nat.choose n j * (-1 : ℤ)^j * (-1 : ℤ)^v) := by
  refine Finset.sum_congr rfl fun and β=> Finset.sum_congr rfl fun and x =>(congr_arg₂ _ (mod_cast(symm) ?_) (pow_add _ _ _)).trans (mul_assoc _ _ _).symm
  aesop(add safe forward Ne)
  by_cases h :2*and_1 -and≤n
  · simp_all only[mul_right_comm _ (n.choose and_1),two_mul,←Nat.choose_symm (n.sub_le_sub_right _ _), mul_le_mul_left',le_add_self,n.add_sub_assoc,Nat.choose_mul]
    push_cast only[*,mul_assoc,mul_left_comm ((n+n).choose (and_1+_)),←Nat.choose_symm (n.sub_le_sub_right _ _),n.add_sub_assoc,Nat.add_le_add,Nat.choose_mul]
    simp_all only[←mul_assoc,←n.choose_symm_add,←Nat.choose_symm (n.sub_le_sub_right _ _),mul_comm ((n+n).choose _),n.add_sub_assoc,le_add_self,Nat.choose_mul]
    exact (congr_arg (· *_ * _) ((congr_arg ↑_ ((Nat.choose_symm_of_eq_add (by valid)).trans (congr_arg₂ ↑_ (by valid) (rfl)))).trans (mul_comm _ _) ) )
  · simp_all only[zero_mul,mul_zero, not_le, true, (by valid:2*n-2*and_1 <n -and),Nat.choose_eq_zero_of_lt]

lemma sum_eq_step2 (n : ℕ) :
  (∑ j ∈ Finset.range (n + 1), ∑ v ∈ Finset.Icc 0 (min n (2 * j)),
    (Nat.choose (2 * n) n * Nat.choose n v * Nat.choose n (2 * j - v) : ℤ) * Nat.choose n j * (-1 : ℤ)^j * (-1 : ℤ)^v) =
  ∑ j ∈ Finset.range (n + 1), (Nat.choose (2 * n) n * Nat.choose n j * (-1 : ℤ)^j : ℤ) *
    ∑ v ∈ Finset.Icc 0 (min n (2 * j)), (Nat.choose n v * Nat.choose n (2 * j - v) : ℤ) * (-1 : ℤ)^v := by
  exact (congr_arg _) ((funext fun and=>.trans (congr_arg @_ (funext fun and=>by ring)) ( Finset.mul_sum _ _ _).symm))

lemma sum_eq_step3 (n : ℕ) :
  (∑ j ∈ Finset.range (n + 1), (Nat.choose (2 * n) n * Nat.choose n j * (-1 : ℤ)^j : ℤ) *
    ∑ v ∈ Finset.Icc 0 (min n (2 * j)), (Nat.choose n v * Nat.choose n (2 * j - v) : ℤ) * (-1 : ℤ)^v) =
  ∑ j ∈ Finset.range (n + 1), (Nat.choose (2 * n) n * Nat.choose n j * (-1 : ℤ)^j : ℤ) * (Nat.choose n j * (-1 : ℤ)^j : ℤ) := by
  have h (j : ℕ) : ∑ v ∈ Finset.Icc 0 (min n (2 * j)), (Nat.choose n v * Nat.choose n (2 * j - v) : ℤ) * (-1 : ℤ)^v = (Nat.choose n j : ℤ) * (-1 : ℤ)^j := inner_sum_eq n j
  simp_all? only

lemma sum_eq_step4 (n : ℕ) :
  (∑ j ∈ Finset.range (n + 1), (Nat.choose (2 * n) n * Nat.choose n j * (-1 : ℤ)^j : ℤ) * (Nat.choose n j * (-1 : ℤ)^j : ℤ)) =
  (Nat.choose (2 * n) n : ℤ) * ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℤ)^2 := by
  exact ( Finset.sum_congr rfl fun and x =>by cases and.even_or_odd with use (by valid :).neg_pow (1 : ℤ)▸by ring).trans (Finset.mul_sum _ _ _).symm

lemma sum_eq (n : ℕ) :
  (∑ j ∈ Finset.range (n + 1), ∑ v ∈ Finset.Icc 0 (min n (2 * j)),
    (Nat.choose (2 * n) (2 * j) * Nat.choose n j * Nat.choose (2 * n - 2 * j) (n - v) * Nat.choose (2 * j) v : ℤ) * (-1 : ℤ)^(j + v)) =
  (Nat.choose (2 * n) n : ℤ) * ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℤ)^2 := by
  have h1 := sum_eq_step1 n
  have h2 := sum_eq_step2 n
  have h3 := sum_eq_step3 n
  have h4 := sum_eq_step4 n
  convert h2.trans (.trans h3 @ h4)

lemma sum_choose_sq (n : ℕ) :
  ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℤ)^2 = (Nat.choose (2 * n) n : ℤ) := by
  rw [←eq_comm, two_mul, n.add_choose_eq]
  simp_all[sq, Finset.Nat.antidiagonal_eq_map _, Finset.mem_range_succ_iff.1]

lemma coeff_H_sum_eq_step1 (n : ℕ) :
  MvPolynomial.coeff (yz_pow_n n) (∑ j ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * j) * Nat.choose n j : P) * (-1 : P)^j * (X 1 + X 2 : P)^(2 * n - 2 * j) * (X 1 - X 2 : P)^(2 * j)) =
  ∑ j ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * j) * Nat.choose n j : ℤ) * (-1 : ℤ)^j *
    MvPolynomial.coeff (yz_pow_n n) ((X 1 + X 2 : P)^(2 * n - 2 * j) * (X 1 - X 2 : P)^(2 * j)) := by
  exact(MvPolynomial.coeff_sum _ _ _).trans ((congr_arg _)<|funext fun and=>.trans (congr_arg _ (mul_assoc _ _ _)) (mod_cast MvPolynomial.coeff_C_mul _ _ _))

lemma expand_X1_X2_pow (k j : ℕ) :
  ((X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j)) =
  (∑ u ∈ Finset.range (k + 1), (Nat.choose k u : P) * (X 1)^(k - u) * (X 2)^u) *
  (∑ v ∈ Finset.range (2 * j + 1), (Nat.choose (2 * j) v : P) * (X 1)^(2 * j - v) * (- X 2)^v) := by
  exact (.trans (by rw [@add_comm, sub_eq_neg_add, add_pow, add_pow]) ((congr_arg₂ _) ((congr_arg _) ((funext fun and=>by ring!))) (congr_arg @_ (funext fun and=>by ring!))))

lemma expand_X1_X2_pow_mul (k j : ℕ) :
  ((X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j)) =
  ∑ u ∈ Finset.range (k + 1), ∑ v ∈ Finset.range (2 * j + 1),
    (Nat.choose k u * Nat.choose (2 * j) v : P) * (-1 : P)^v * (X 1)^(k - u + 2 * j - v) * (X 2)^(u + v) := by
  push_cast only[add_comm (.X (1) : MvPolynomial (Fin _) Int), sub_eq_neg_add (.X (1) : MvPolynomial (Fin _) Int), add_pow, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun and n=> Finset.sum_congr rfl fun and μ=>Nat.add_sub_assoc (Finset.mem_range_succ_iff.1 μ) _▸by ring

lemma coeff_expand_X1_X2_pow_mul (n k j : ℕ) (h : k + 2 * j = 2 * n) :
  MvPolynomial.coeff (yz_pow_n n) ((X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j)) =
  ∑ u ∈ Finset.range (k + 1), ∑ v ∈ Finset.range (2 * j + 1),
    (Nat.choose k u * Nat.choose (2 * j) v : ℤ) * (-1 : ℤ)^v *
    MvPolynomial.coeff (yz_pow_n n) ((X 1 : P)^(2 * n - u - v) * (X 2 : P)^(u + v)) := by
  push_cast only [add_comm (.X (1) : MvPolynomial (Fin _) Int), sub_eq_neg_add (.X (1) : MvPolynomial (Fin _) Int), add_pow, Finset.sum_mul_sum,<-h]
  refine(MvPolynomial.coeff_sum _ _ _).trans (Finset.sum_congr rfl fun and μ=>(MvPolynomial.coeff_sum _ _ _).trans (Finset.sum_congr rfl fun and β=>.trans (? _) (MvPolynomial.coeff_C_mul _ _ _)))
  exact (congr_arg _)<|symm (.trans (by rw [k.sub_add_comm (Finset.mem_range_succ_iff.1 μ),Nat.add_sub_assoc (Finset.mem_range_succ_iff.1 β),map_mul,map_mul,map_pow, map_neg, map_one])<|by ring!)

lemma coeff_yz_pow_n_monomial (n A B : ℕ) :
  MvPolynomial.coeff (yz_pow_n n) ((X 1 : P)^A * (X 2 : P)^B) = if A = n ∧ B = n then 1 else 0 := by
  norm_num [yz_pow_n, MvPolynomial.coeff_mul,MvPolynomial.coeff_X_pow]
  norm_num[xyz_pow_n, and_comm,←ite_and]
  aesop
  · refine Finset.card_eq_one.mpr ⟨(.single (1) B,.single (2) B), Finset.ext fun(x, y)=> Finset.mem_filter.trans ⟨by simp_all, fun and=>⟨ Finset.mem_antidiagonal.mpr (Finsupp.ext ? _),by simp_all⟩⟩⟩
    simp_all[Vars, Finsupp.update]
    simp_all[ Fin.forall_iff_succ]
    trivial
  · simp_all-contextual[Vars, Finsupp.ext_iff, Fin.forall_iff_succ]
    aesop

lemma coeff_expand_X1_X2_eval (n k j : ℕ) (h : k + 2 * j = 2 * n) :
  (∑ u ∈ Finset.range (k + 1), ∑ v ∈ Finset.range (2 * j + 1),
    (Nat.choose k u * Nat.choose (2 * j) v : ℤ) * (-1 : ℤ)^v *
    (if 2 * n - u - v = n ∧ u + v = n then 1 else 0)) =
  ∑ v ∈ Finset.Icc 0 (min n (2 * j)), (Nat.choose k (n - v) * Nat.choose (2 * j) v : ℤ) * (-1 : ℤ)^v := by
  refine Finset.sum_comm.trans ( Finset.range_eq_Ico▸(Finset.sum_subset (Finset.Icc_subset_Icc_right (inf_le_right)) (by simp_all[mt ↑le_add_self.trans_eq])).symm.trans ( Finset.sum_congr ↑rfl fun and (M) =>?_) )
  if R:n-and≤k then rw[ Finset.sum_eq_single_of_mem (n-and) ( Finset.mem_Ico.2 (by valid)) (fun _ _ _=>by rw [if_neg (by valid),mul_zero]),if_pos (( Finset.mem_Icc.1 M).elim (by valid)),mul_one]else _
  exact (k.choose_eq_zero_of_lt (not_le.1 R)).symm▸.trans ( Finset.sum_eq_zero fun and α=>by rw [if_neg (( Finset.mem_Icc.1 α).elim (by valid)),mul_zero]) (by ring)

lemma poly_coeff_eq_sum_icc (n j : ℕ) :
  Polynomial.coeff ((1 + Polynomial.X : Polynomial ℤ)^(2 * n - 2 * j) * (1 - Polynomial.X : Polynomial ℤ)^(2 * j)) n =
  ∑ v ∈ Finset.Icc 0 (min n (2 * j)), (Nat.choose (2 * n - 2 * j) (n - v) * Nat.choose (2 * j) v : ℤ) * (-1 : ℤ)^v := by
  rw [←Nat.range_succ_eq_Icc_zero, two_mul,@mul_comm, sub_eq_neg_add, add_pow]
  norm_num[mul_comm ((_-2*j).choose _ : ℤ),Finset.sum_mul,mul_assoc]
  convert(Finset.sum_subset _ _).symm using 2
  · cases‹ℕ›.even_or_odd with exact(((congr_arg _) ↑(Nat.add_sub_of_le (( Finset.mem_range_succ_iff.1 (by valid)).trans (inf_le_left)))).symm.trans (by simp_all[coeff_one_add_X_pow, Odd.neg_pow,coeff_X_pow_mul'])).symm
  · exact (List.range_subset.2 (by push_cast[min_le_right]))
  · use (by cases·.even_or_odd with simp_all[coeff_X_pow_mul',Nat.succ_le, Odd.neg_pow,n.lt_add_right,Nat.lt_succ])

lemma coeff_yz_pow_n_X1_X2_pow (n j : ℕ) (hj : j ≤ n) :
  MvPolynomial.coeff (yz_pow_n n) ((X 1 + X 2 : P)^(2 * n - 2 * j) * (X 1 - X 2 : P)^(2 * j)) =
  ∑ v ∈ Finset.Icc 0 (min n (2 * j)), (Nat.choose (2 * n - 2 * j) (n - v) * Nat.choose (2 * j) v : ℤ) * (-1 : ℤ)^v := by
  have h1 : (2 * n - 2 * j) + 2 * j = 2 * n := by
    exact (Nat.sub_add_cancel (by gcongr))
  have h2 := coeff_expand_X1_X2_pow_mul n (2 * n - 2 * j) j h1
  have h3 := coeff_expand_X1_X2_eval n (2 * n - 2 * j) j h1
  simp_all -contextual only[yz_pow_n, add_pow, sub_eq_add_neg, MvPolynomial.coeff_mul,mul_assoc, MvPolynomial.coeff_X_pow]
  refine h3▸ Finset.sum_congr rfl fun A B=> Finset.sum_congr rfl fun and x =>(congr_arg _) ((congr_arg _) ((congr_arg _) @?_))
  split
  · norm_num[*,xyz_pow_n]
    rw[ Finset.sum_eq_single (.single (1) (n : ℕ),.single (2) n) (fun _ _ _=>by_contra (by bound))]
    · norm_num
    norm_num+decide[Vars, Finsupp.ext_iff, Fin.forall_iff_succ]
    norm_num [ Finsupp.ofSupportFinite]
  · refine Finset.sum_eq_zero fun and μ=>by_contra fun and=>absurd ((congr_arg fun and=> (and (1), and (2))) ( Finset.mem_antidiagonal.1 μ)) ?_
    norm_num+decide[xyz_pow_n,←not_not.1 (left_ne_zero_of_mul and ∘ (if_neg ·)),←not_not.1 (right_ne_zero_of_mul and ∘ (if_neg ·)), *]
    use fun and=>by valid ∘And.intro and

lemma coeff_H_sum_eq_step2 (n : ℕ) :
  ∑ j ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * j) * Nat.choose n j : ℤ) * (-1 : ℤ)^j *
    MvPolynomial.coeff (yz_pow_n n) ((X 1 + X 2 : P)^(2 * n - 2 * j) * (X 1 - X 2 : P)^(2 * j)) =
  ∑ j ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * j) * Nat.choose n j : ℤ) * (-1 : ℤ)^j *
    ∑ v ∈ Finset.Icc 0 (min n (2 * j)), (Nat.choose (2 * n - 2 * j) (n - v) * Nat.choose (2 * j) v : ℤ) * (-1 : ℤ)^v := by
  have h2 : ∀ j ∈ Finset.range (n + 1), MvPolynomial.coeff (yz_pow_n n) ((X 1 + X 2 : P)^(2 * n - 2 * j) * (X 1 - X 2 : P)^(2 * j)) = ∑ v ∈ Finset.Icc 0 (min n (2 * j)), (Nat.choose (2 * n - 2 * j) (n - v) * Nat.choose (2 * j) v : ℤ) * (-1 : ℤ)^v := by
    intros j hj
    have hj2 : j ≤ n := by rwa[ ← Finset.mem_range_succ_iff]
    exact coeff_yz_pow_n_X1_X2_pow n j hj2
  simp_all only[]

lemma coeff_H_sum_eq_step3 (n : ℕ) :
  ∑ j ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * j) * Nat.choose n j : ℤ) * (-1 : ℤ)^j *
    ∑ v ∈ Finset.Icc 0 (min n (2 * j)), (Nat.choose (2 * n - 2 * j) (n - v) * Nat.choose (2 * j) v : ℤ) * (-1 : ℤ)^v =
  ∑ j ∈ Finset.range (n + 1), ∑ v ∈ Finset.Icc 0 (min n (2 * j)),
    (Nat.choose (2 * n) (2 * j) * Nat.choose n j * Nat.choose (2 * n - 2 * j) (n - v) * Nat.choose (2 * j) v : ℤ) * (-1 : ℤ)^(j + v) := by
  push_cast only[mul_assoc,mul_left_comm ((-1) ^ _), Finset.mul_sum,pow_add]

lemma coeff_H_sum_eq (n : ℕ) :
  MvPolynomial.coeff (yz_pow_n n) (∑ j ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * j) * Nat.choose n j : P) * (-1 : P)^j * (X 1 + X 2 : P)^(2 * n - 2 * j) * (X 1 - X 2 : P)^(2 * j)) =
  ∑ j ∈ Finset.range (n + 1), ∑ v ∈ Finset.Icc 0 (min n (2 * j)),
    (Nat.choose (2 * n) (2 * j) * Nat.choose n j * Nat.choose (2 * n - 2 * j) (n - v) * Nat.choose (2 * j) v : ℤ) * (-1 : ℤ)^(j + v) := by
  have h1 := coeff_H_sum_eq_step1 n
  have h2 := coeff_H_sum_eq_step2 n
  have h3 := coeff_H_sum_eq_step3 n
  convert h2.trans ↑h3 with S

lemma coeff_X0_mul_X12_step1 (n A k j : ℕ) :
  MvPolynomial.coeff (xyz_pow_n n) ((1 + X 0 : P)^A * (X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j)) =
  MvPolynomial.coeff (xyz_pow_n n) ((∑ u ∈ Finset.range (A + 1), (Nat.choose A u : P) * (X 0)^u) * (X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j)) := by
  exact (congr_arg _) ((congr_arg (.*_* _) ((.trans (by rw [add_comm, add_pow]) ((congr_arg _) ((funext fun and=>by ring!)))))))

lemma coeff_X0_mul_X12_step2 (n A k j : ℕ) :
  MvPolynomial.coeff (xyz_pow_n n) ((∑ u ∈ Finset.range (A + 1), (Nat.choose A u : P) * (X 0)^u) * (X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j)) =
  ∑ u ∈ Finset.range (A + 1), (Nat.choose A u : ℤ) * MvPolynomial.coeff (xyz_pow_n n) ((X 0)^u * ((X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j))) := by
  exact (.trans (by rw [ Finset.sum_mul, Finset.sum_mul,MvPolynomial.coeff_sum]) ((congr_arg _) ((funext fun and=>.trans (by rw [mul_assoc,mul_assoc]) (by apply MvPolynomial.coeff_C_mul)))))

lemma coeff_X0_mul_X12_step3 (n u k j : ℕ) (hu : u ≠ n) :
  MvPolynomial.coeff (xyz_pow_n n) ((X 0)^u * ((X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j))) = 0 := by
  norm_num[xyz_pow_n,add_pow,MvPolynomial.coeff_mul,MvPolynomial.coeff_X_pow]at*
  refine Finset.sum_eq_zero fun and x =>ite_eq_right_iff.2 fun and' => Finset.sum_eq_zero fun and x =>.trans (by rw [MvPolynomial.coeff_sum, Finset.sum_mul]) (Finset.sum_eq_zero fun and h=>.trans (by rw [sub_pow]) ? _)
  norm_num[mul_assoc, MvPolynomial.coeff_sum, and'.symm,← Finset.mem_antidiagonal.1 x]at*
  use or_iff_not_imp_left.2 (Finset.sum_eq_zero ∘ fun and a s=>mod_cast(MvPolynomial.coeff_C_mul _ _ _).trans.comp (mul_eq_zero_of_right _) ? _)
  norm_num[←mul_assoc, MvPolynomial.coeff_mul, Finsupp.ext_iff,MvPolynomial.coeff_X_pow]at*
  refine Finset.sum_eq_zero fun and c=> if a:_=0 then(mul_eq_zero_of_left (Finset.sum_eq_zero fun and m=>symm ? _) _)else(mul_eq_zero_of_right _) (MvPolynomial.coeff_C _ _|>.trans (if_neg (Ne.symm a)))
  refine(ite_eq_right_iff.2 fun and=>if_neg fun and' =>‹¬_› (Finset.sum_eq_zero fun and β=>? _)).symm
  refine if I:_=0 then(mul_eq_zero_of_left (Finset.sum_eq_zero fun and k=>ite_eq_right_iff.2 fun and=>if_neg fun and=>absurd (x 0) ? _) _)else(mul_eq_zero_of_right _).comp ( MvPolynomial.coeff_C _ _).trans (if_neg (Ne.symm I))
  norm_num+decide[I,hu,a,← Finset.mem_antidiagonal.1 β,← Finset.mem_antidiagonal.1 c,← Finset.mem_antidiagonal.1 m,← Finset.mem_antidiagonal.1 k,←and,←and',←‹∀_, _-_ = _›]
  exact (congr_arg _ (.symm (by apply_rules))).trans_ne (by norm_num+decide[hu, Finsupp.ofSupportFinite])

lemma coeff_X0_mul_X12_step4 (n k j : ℕ) :
  MvPolynomial.coeff (xyz_pow_n n) ((X 0)^n * ((X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j))) =
  MvPolynomial.coeff (yz_pow_n n) ((X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j)) := by
  replace:xyz_pow_n n=.single 0 n+yz_pow_n n
  · delta xyz_pow_n yz_pow_n
    norm_num[ Finsupp.single_apply, Finsupp.update, Finsupp.ext_iff,comm]
    aesop
  · simp_all[MvPolynomial.X_pow_eq_monomial]

lemma coeff_X0_mul_X12_step5 (n A k j : ℕ) :
  ∑ u ∈ Finset.range (A + 1), (Nat.choose A u : ℤ) * MvPolynomial.coeff (xyz_pow_n n) ((X 0)^u * ((X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j))) =
  (Nat.choose A n : ℤ) * MvPolynomial.coeff (xyz_pow_n n) ((X 0)^n * ((X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j))) := by
  have h3 (u : ℕ) (hu : u ≠ n) : MvPolynomial.coeff (xyz_pow_n n) ((X 0)^u * ((X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j))) = 0 := coeff_X0_mul_X12_step3 n u k j hu
  exact Finset.sum_eq_single n ( fun and R L=>by rw [h3 and L,mul_zero]) fun and=> A.choose_eq_zero_of_lt (not_lt.1 (and.comp (List.mem_range.2)))▸by valid

lemma coeff_X0_mul_X12 (n A k j : ℕ) :
  MvPolynomial.coeff (xyz_pow_n n) ((1 + X 0 : P)^A * (X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j)) =
  (Nat.choose A n : ℤ) * MvPolynomial.coeff (yz_pow_n n) ((X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j)) := by
  have h1 := coeff_X0_mul_X12_step1 n A k j
  have h2 := coeff_X0_mul_X12_step2 n A k j
  have h5 := coeff_X0_mul_X12_step5 n A k j
  have h4 := coeff_X0_mul_X12_step4 n k j
  simp_all-contextual only

lemma coeff_yz_eq_zero_of_ne (n k j : ℕ) (h : k + 2 * j ≠ 2 * n) :
  MvPolynomial.coeff (yz_pow_n n) ((X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j)) = 0 := by
  push_cast [yz_pow_n, sub_pow, add_pow, MvPolynomial.coeff_mul, Ne] at h⊢
  push_cast only[xyz_pow_n, two_mul,mul_assoc, MvPolynomial.coeff_sum, Finset.sum_mul_sum] at h⊢
  refine Finset.sum_eq_zero fun and x => Finset.sum_eq_zero fun and μ=> Finset.sum_eq_zero fun and β=>mod_cast(((congr_arg _) (MvPolynomial.coeff_C_mul _ _ _)).trans) ?_
  norm_num[←mul_assoc, MvPolynomial.coeff_mul,eq_comm, MvPolynomial.coeff_X_pow]at*
  use or_iff_not_imp_left.2 fun and=>symm (Finset.sum_eq_zero fun and i=> if a:and.2=0 then(mul_eq_zero_of_left (Finset.sum_eq_zero fun and x =>(symm) ? _) _)else(mul_eq_zero_of_right _) ((MvPolynomial.coeff_C _ _).trans (if_neg (Ne.symm a))))
  refine(ite_eq_right_iff.2 fun and=>if_neg (by valid ∘Or.inl ∘symm ∘ Finset.sum_eq_zero ∘ fun and a s=>.trans (congr_arg _ (MvPolynomial.coeff_C _ _)) ? _)).symm
  use(em _).elim (if_pos ·▸mul_eq_zero_of_left (Finset.sum_eq_zero fun and j=>ite_eq_right_iff.2 fun and=>if_neg fun and=>(h) ? _) _) (if_neg ·▸mul_zero _)
  norm_num+decide[*,← Finset.mem_antidiagonal.1 j,← Finset.mem_antidiagonal.1 x,← Finset.mem_antidiagonal.1 i,← Finset.mem_antidiagonal.1 s,←‹0 = a.2›, Finsupp.ext_iff]at‹_+_ = _›
  linear_combination2(norm:=norm_num+decide[ μ, β,add_add_add_comm])(x (2)).symm+(x (1)).symm
  norm_num+decide[Finsupp.ofSupportFinite]

lemma P_n_double_sum (n : ℕ) : P_n n =
  ∑ k ∈ Finset.range (2 * n + 1), ∑ j ∈ Finset.range (n + 1),
    (Nat.choose (2 * n) k * Nat.choose n j : P) * (-1 : P)^j *
    (1 + X 0)^(4 * n - k - 2 * j) * (X 1 + X 2)^k * (X 1 - X 2)^(2 * j) := by
  push_cast only[P_n,pow_mul,Nat.sub_sub]
  show _=∑ a ∈ _,∑x ∈ _,(id _)*(id _)*_*_*_*_
  have := (add_pow (.X (1)+.X (2) : MvPolynomial (Fin 03) Int) (1+.X 0) (2*(n)):).symm
  rw [←pow_mul,add_assoc,add_comm (1+ _),←this, Finset.sum_mul, Finset.sum_mul, Finset.sum_congr rfl fun and Y=>?_]
  have := (add_pow (-(.X (1)-.X 2)^2 : MvPolynomial (Fin 3) Int) ((1+.X 0)^2) n).symm
  refine .trans (by rw [mul_assoc,←mul_pow,(congr_arg (.^ _) (by ring)).trans this.symm, Finset.mul_sum]) (Finset.sum_congr rfl fun R M=>? _)
  exact (.trans (by rw [←pow_mul,neg_pow]) (.symm (.trans (by rw [id,id, (by match List.mem_range.1 M,List.mem_range.1 Y with|A, B=>omega:_- (and+ _)=2*n-and+2*(n-R))]) (by ring!))))

lemma coeff_P_n_eq_step1 (n : ℕ) :
  MvPolynomial.coeff (xyz_pow_n n) (P_n n) =
  ∑ k ∈ Finset.range (2 * n + 1), ∑ j ∈ Finset.range (n + 1),
    (Nat.choose (2 * n) k * Nat.choose n j : ℤ) * (-1 : ℤ)^j *
    MvPolynomial.coeff (xyz_pow_n n) ((1 + X 0 : P)^(4 * n - k - 2 * j) * (X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j)) := by
  have h1 := P_n_double_sum n
  push_cast only[mul_assoc, true,h1, MvPolynomial.coeff_sum]
  exact (congr_arg _) ((funext fun and=>congr_arg _ (funext fun and=>mod_cast MvPolynomial.coeff_C_mul _ _ _|>.trans (congr_arg _ ((MvPolynomial.coeff_C_mul _ _ _).trans ((congr_arg _) (MvPolynomial.coeff_C_mul _ _ _)))))))

lemma coeff_P_n_eq_step2 (n : ℕ) :
  MvPolynomial.coeff (xyz_pow_n n) (P_n n) =
  ∑ k ∈ Finset.range (2 * n + 1), ∑ j ∈ Finset.range (n + 1),
    (Nat.choose (2 * n) k * Nat.choose n j : ℤ) * (-1 : ℤ)^j *
    (Nat.choose (4 * n - k - 2 * j) n : ℤ) *
    MvPolynomial.coeff (yz_pow_n n) ((X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j)) := by
  have h1 := coeff_P_n_eq_step1 n
  have h2 (k j : ℕ) : MvPolynomial.coeff (xyz_pow_n n) ((1 + X 0 : P)^(4 * n - k - 2 * j) * (X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j)) = (Nat.choose (4 * n - k - 2 * j) n : ℤ) * MvPolynomial.coeff (yz_pow_n n) ((X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j)) := coeff_X0_mul_X12 n (4 * n - k - 2 * j) k j
  push_cast only[mul_assoc _ ((_: ℕ) : ℤ), *]

lemma coeff_P_n_eq_step2_5 (n : ℕ) :
  ∑ k ∈ Finset.range (2 * n + 1), ∑ j ∈ Finset.range (n + 1),
    (Nat.choose (2 * n) k * Nat.choose n j : ℤ) * (-1 : ℤ)^j *
    (Nat.choose (4 * n - k - 2 * j) n : ℤ) *
    MvPolynomial.coeff (yz_pow_n n) ((X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j)) =
  ∑ j ∈ Finset.range (n + 1),
    (Nat.choose (2 * n) (2 * n - 2 * j) * Nat.choose n j : ℤ) * (-1 : ℤ)^j *
    (Nat.choose (4 * n - (2 * n - 2 * j) - 2 * j) n : ℤ) *
    MvPolynomial.coeff (yz_pow_n n) ((X 1 + X 2 : P)^(2 * n - 2 * j) * (X 1 - X 2 : P)^(2 * j)) := by
  have h2 (k j : ℕ) (hkj : k + 2 * j ≠ 2 * n) : MvPolynomial.coeff (yz_pow_n n) ((X 1 + X 2 : P)^k * (X 1 - X 2 : P)^(2 * j)) = 0 := coeff_yz_eq_zero_of_ne n k j hkj
  exact Finset.sum_comm.trans (congr_arg ↑( _) ((funext fun and=> Finset.sum_eq_single_of_mem @_ ↑(List.mem_range.mpr (by valid) ) fun and I I =>by rw [h2 _ _ (I ∘Nat.eq_sub_of_add_eq),mul_zero])))

lemma coeff_P_n_eq_proof (n : ℕ) :
  MvPolynomial.coeff (xyz_pow_n n) (P_n n) =
  ∑ j ∈ Finset.range (n + 1),
    (Nat.choose (2 * n) (2 * n - 2 * j) * Nat.choose n j : ℤ) * (-1 : ℤ)^j *
    (Nat.choose (4 * n - (2 * n - 2 * j) - 2 * j) n : ℤ) *
    MvPolynomial.coeff (yz_pow_n n) ((X 1 + X 2 : P)^(2 * n - 2 * j) * (X 1 - X 2 : P)^(2 * j)) := by
  have h1 := coeff_P_n_eq_step2 n
  have h3 := coeff_P_n_eq_step2_5 n
  convert @h3
lemma coeff_P_n_eq_step4 (n : ℕ) :
  MvPolynomial.coeff (xyz_pow_n n) (P_n n) =
  (Nat.choose (2 * n) n : ℤ) * ∑ j ∈ Finset.range (n + 1),
    (Nat.choose (2 * n) (2 * j) * Nat.choose n j : ℤ) * (-1 : ℤ)^j *
    MvPolynomial.coeff (yz_pow_n n) ((X 1 + X 2 : P)^(2 * n - 2 * j) * (X 1 - X 2 : P)^(2 * j)) := by
  have h1 := coeff_P_n_eq_proof n
  simp_all only[mul_assoc, mul_left_comm ((2*n).choose n : ℤ),←Nat.sub_mul,← Finset.mem_range_succ_iff,Nat.sub_sub, mul_le_mul_left',Nat.sub_add_cancel,Nat.choose_symm, Finset.mul_sum]

lemma coeff_P_n_eq_step5 (n : ℕ) :
  MvPolynomial.coeff (xyz_pow_n n) (P_n n) =
  (Nat.choose (2 * n) n : ℤ) * ∑ j ∈ Finset.range (n + 1), ∑ v ∈ Finset.Icc 0 (min n (2 * j)),
    (Nat.choose (2 * n) (2 * j) * Nat.choose n j * Nat.choose (2 * n - 2 * j) (n - v) * Nat.choose (2 * j) v : ℤ) * (-1 : ℤ)^(j + v) := by
  have h1 := coeff_P_n_eq_step4 n
  have h2 := coeff_H_sum_eq n
  exact h1.trans (congr_arg _ (h2▸symm ((MvPolynomial.coeff_sum _ _ _).trans ((congr_arg _) ((funext fun and=>.trans (by rw [mul_assoc]) (by exact_mod_cast MvPolynomial.coeff_C_mul _ _ _)))))))

-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (n : ℕ) : (a n : ℤ) = MvPolynomial.coeff (xyz_pow_n n) (P_n n) := by
  -- EVOLVE-BLOCK-START
  have h1 := coeff_P_n_eq_step5 n
  have h2 := sum_eq n
  have h3 : (a n : ℤ) = (Nat.choose (2 * n) n : ℤ) ^ 3 := by norm_cast
  simp_all-contextual only[pow_three, two_mul,sq,n.add_choose_eq,Nat.cast_sum,Nat.cast_mul]
  norm_num[Finset.Nat.antidiagonal_eq_map,Finset.sum_congr rfl fun a s=>congr_arg _ (Nat.cast_inj.2 (n.choose_symm _))]
  -- EVOLVE-BLOCK-END
