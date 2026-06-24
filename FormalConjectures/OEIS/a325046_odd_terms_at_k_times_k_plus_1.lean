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

open Finset

/--
A325046: G.f.: $\sum_{n \ge 0} x^n \cdot \frac{(1 + x^n)^n}{(1 - x^{n+1})^{n+1}}$.

The term $a(N)$ is the coefficient of $x^N$ in the generating function.
Expanding the terms, we get a formula for $a(N)$:
$$a(N) = \sum_{n=0}^N \sum_{k=0}^n \mathbf{1}_{n + nk + (n+1)j = N} \binom{n}{k} \binom{n+j}{j}$$
where $j = \frac{N - n(k+1)}{n+1}$.
-/
def a (N : ℕ) : ℕ :=
  -- The outer sum runs over $n$ from $0$ to $N$.
  (range (N + 1)).sum (fun n =>
    -- The inner sum runs over $k$ from $0$ to $n$.
    (range (n + 1)).sum (fun k =>
      let R : ℕ := N - n * (k + 1)
      let m : ℕ := n + 1
      -- We require $R = N - n(k+1) \ge 0$ and $m = n+1$ must divide $R$.
      if n * (k + 1) ≤ N ∧ R % m = 0 then
        -- $j = R / m$.
        let j : ℕ := R / m
        -- The summand is $\binom{n}{k} \binom{n+j}{j}$.
        n.choose k * (n + j).choose j
      else
        0
    )
  )

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
lemma sum_involution_zmod2 {α : Type} [DecidableEq α] (S : Finset α) (I : α → α) (f : α → ZMod 2)
    (hI_mem : ∀ x ∈ S, I x ∈ S)
    (hI_inv : ∀ x ∈ S, I (I x) = x)
    (hf_I : ∀ x ∈ S, f (I x) = f x) :
    ∑ x ∈ S, f x = ∑ x ∈ S.filter (fun x => I x = x), f x := by
  have h_split : ∑ x ∈ S, f x = ∑ x ∈ S.filter (fun x => I x = x), f x + ∑ x ∈ S.filter (fun x => I x ≠ x), f x := by
    rw [@S.sum_filter_add_sum_filter_not]
  have h_zero : ∑ x ∈ S.filter (fun x => I x ≠ x), f x = 0 := by
    apply Finset.sum_involution (g := fun x _ => I x)
    · refine fun and (a) => (hf_I and (( S.filter_subset _) a)).symm▸two_mul (f _)▸zero_mul (f _)
    · norm_num+contextual
    · grind
    · grind
  rw [h_split, h_zero, add_zero]

def V (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Iic N ×ˢ Finset.Iic N).filter fun p =>
    p.2 ≤ p.1 ∧ p.1 * (p.2 + 1) ≤ N ∧ (N - p.1 * (p.2 + 1)) % (p.1 + 1) = 0

def I_map (N : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  let n := p.1
  let k := p.2
  let j := (N - n * (k + 1)) / (n + 1)
  (k + j, k)

def T (N : ℕ) (p : ℕ × ℕ) : ℕ :=
  let n := p.1
  let k := p.2
  let j := (N - n * (k + 1)) / (n + 1)
  n.choose k * (n + j).choose j

lemma a_eq_sum_T (N : ℕ) : a N = ∑ p ∈ V N, T N p := by
  delta a and V and T Finset.sum
  refine show∑ a ∈.range _,∑n ∈.range _,_=∑ a ∈_, _ from Finset.range_eq_Ico▸symm.comp ( Finset.sum_filter _ _).trans (.trans ( Finset.sum_product _ _ _) ( Finset.sum_congr rfl fun and x =>?_))
  exact ( Finset.sum_subset (Finset.Icc_subset_Iic_self.trans (by simp_all [and.lt_succ])) fun and A B =>if_neg (B.comp ( Finset.mem_Iic.mpr ·.1))).symm.trans ( Finset.sum_congr rfl (by simp_all [·.lt_succ]))

lemma I_mem_V {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ V N) : I_map N p ∈ V N := by
  delta I_map and V at *
  simp_all[ (by nlinarith[ Finset.mem_filter.1 hp, N.sub_add_cancel (Finset.mem_filter.1 hp).2.2.1, (N-p.1*(p.2 + 1)).mul_div_le (p.1+1)]:p.2+ (N-p.1*(p.2 + 1))/(p.1+1)≤N)]
  use (by nlinarith[hp.2.2.2▸Nat.mod_add_div _ _ , N.sub_add_cancel hp.2.2.1]),Nat.mod_eq_zero_of_dvd ⟨p.1-p.2, N.sub_eq_of_eq_add ?_⟩
  linear_combination-.add_sub_of_le hp.2.1*(p.2+_/_+1)-N.sub_add_cancel hp.2.2.1-.div_mul_cancel (Nat.dvd_of_mod_eq_zero hp.2.2.2)

lemma I_I_eq {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ V N) : I_map N (I_map N p) = p := by
  simp_all[I_map, V]
  rw[Nat.div_eq_of_eq_mul_left (by bound) (N.sub_eq_of_eq_add (by nlinarith only[hp.2.2.2▸Nat.mod_add_div _ _ , N.sub_add_cancel hp.2.2.1,Nat.sub_add_cancel hp.2.1]):_=(p.1-p.2) *_)]
  simp_rw [Nat.add_sub_of_le hp.2.1]

lemma T_I_eq {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ V N) : T N (I_map N p) = T N p := by
  norm_num[I_mapAd /em, T, V]at *
  simp_all[I_map,Nat.choose_mul]
  cases Nat.exists_eq_add_of_le hp.2.left
  simp_all[p.2.choose_symm_add, add_right_comm p.2 (by valid),mul_comm (by valid),Nat.choose_mul]
  simp_all[mul_comm ((_+‹ℕ›).choose _),Nat.mul_div_assoc _,Nat.dvd_iff_mod_eq_zero, add_assoc, add_mul,Nat.choose_mul]
  rw[(Nat.div_eq_of_eq_mul_left (by bound) (N.sub_eq_of_eq_add (by linarith[hp.2.2▸Nat.mod_add_div _ _ , N.sub_add_cancel hp.2.1])):_/(p.2+(_+1))=by valid),mul_comm]
  norm_num[p.2.choose_symm_add, add_left_comm p.2,Nat.choose_mul,mul_assoc]
  norm_num[p.2.choose_symm_add, ← add_assoc,add_comm (p.snd), true,Nat.choose_mul,Nat.choose_symm_add]
  zify[le_self_add, add_assoc,Nat.choose_mul,Nat.choose_symm_add,Nat.add_sub_cancel_left]
  rw [←add_left_comm,Nat.add_sub_cancel_left]

lemma T_even_step1 (n k : ℕ) (hk : k ≤ n) :
    n.choose k * (2 * n - k).choose (n - k) = (2 * n - k).choose (2 * (n - k)) * (2 * (n - k)).choose (n - k) := by
  simp_all only[le_add_self,Nat.choose_mul,Nat.add_sub_cancel, two_mul,n.add_sub_assoc,n.choose_symm,mul_comm (n.choose k)]

lemma T_even_step2 (m : ℕ) (hm : 0 < m) : (2 * m).choose m % 2 = 0 := by
  rw [←Nat.mul_mod_right _,Nat.choose_mul_right hm.ne']

lemma T_even_of_lt (n k : ℕ) (hk : k < n) : (n.choose k * (2 * n - k).choose (n - k)) % 2 = 0 := by
  rw [←Nat.even_iff,two_mul,n.add_sub_assoc (by gcongr),n.add_choose_eq,mul_comm]
  simp_all[mul_comm, mul_assoc,Nat.even_iff,Nat.choose_symm (Finset.mem_range_succ_iff.1 _), Finset.mul_sum, Finset.Nat.antidiagonal_eq_map]
  obtain ⟨M, rfl⟩:=k.exists_eq_add_of_le hk.le
  have' := M.sum_range_choose▸ Finset.mul_sum _ _ <|(k+ M).choose k
  refine(k.add_sub_cancel_left M).symm▸.trans (? _) (this▸(dvd_pow_self (2 : ℕ) (by·omega)).mul_left ↑(_)).modEq_zero_nat
  refine(Finset.sum_nat_mod _ _ _).trans.comp (congr_arg (·%2) ( Finset.sum_congr rfl fun and β=>k.choose_symm_add▸?_)).trans ( Finset.sum_nat_mod _ _ _).symm
  simp_all[mul_left_comm ((k+M).choose M),Nat.choose_mul,Nat.mod_two_of_bodd, and.lt_succ]

lemma fixed_point_imp (N : ℕ) (p : ℕ × ℕ) (hp : p ∈ V N) (hI : I_map N p = p) (hk : p.1 = p.2) :
  N = p.1 * (p.1 + 1) := by
  norm_num[I_map, V, mul_add,←hk,Prod.ext_iff]at *
  match hp.2.2▸Nat.mod_eq_of_lt with | S=>omega
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (N : ℕ) : a N % 2 = 1 → ∃ k : ℕ, N = k * (k + 1) := by
  -- EVOLVE-BLOCK-START
  intro ha
  have ha2 : (a N : ZMod 2) = 1 := by
    exact (ha▸ZMod.natCast_mod _ _)▸rfl
  have h_sum : (a N : ZMod 2) = ∑ p ∈ V N, (T N p : ZMod 2) := by
    simp_all -contextual[a, T, V]
    simp_all only[ite_and,← Finset.mem_range_succ_iff,← Finset.mem_range,show Finset.Iic N=.range (N+1)by norm_num[ Finset.ext_iff,Nat.lt_succ], Finset.inter_eq_right.2, Finset.sum_filter, Finset.sum_product]
    simp_all only[ ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2,← Finset.mem_range,Nat.succ_le]
    rwa[ Finset.sum_congr rfl fun and β=>by rw [ Finset.inter_eq_right.2 (List.range_subset.2<|List.mem_range.1 β)],eq_comm]
  have h_inv := sum_involution_zmod2 (V N) (I_map N) (fun p => (T N p : ZMod 2)) (fun p hp => I_mem_V hp) (fun p hp => I_I_eq hp) (fun p hp => congrArg Nat.cast (T_I_eq hp))
  rw [h_sum, h_inv] at ha2
  have h_split : ∑ p ∈ (V N).filter (fun p => I_map N p = p), (T N p : ZMod 2) =
    ∑ p ∈ ((V N).filter (fun p => I_map N p = p)).filter (fun p => p.1 = p.2), (T N p : ZMod 2) +
    ∑ p ∈ ((V N).filter (fun p => I_map N p = p)).filter (fun p => p.1 ≠ p.2), (T N p : ZMod 2) := by
    simp_rw [ Finset.sum_filter_add_sum_filter_not]
  rw [h_split] at ha2
  have h_zero : ∑ p ∈ ((V N).filter (fun p => I_map N p = p)).filter (fun p => p.1 ≠ p.2), (T N p : ZMod 2) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have h_V : p ∈ V N := by exact ( Finset.filter_subset _ _ ↑( Finset.filter_subset _ _ hp))
    have h_I : I_map N p = p := by simp_all only [ Finset.mem_filter]
    have h_ne : p.1 ≠ p.2 := by exact ( Finset.mem_filter.mp hp).2
    have h_le : p.2 ≤ p.1 := by norm_num[I_map, true, V,Prod.ext_iff] at h_V h_I
                                apply h_V.2.1
    have h_lt : p.2 < p.1 := lt_of_le_of_ne h_le h_ne.symm
    have hj : (N - p.1 * (p.2 + 1)) / (p.1 + 1) = p.1 - p.2 := by norm_num[I_map, V,Prod.ext_iff]at h_V h_I⊢
                                                                  exact (Nat.eq_sub_of_add_eq') h_I
    have hT_eq : T N p = p.1.choose p.2 * (2 * p.1 - p.2).choose (p.1 - p.2) := by simp_all only[I_map, T, V, two_mul,Ne,Prod.ext_iff,Nat.add_sub_assoc]
    have hT_even : T N p % 2 = 0 := by
      rw [hT_eq]
      exact T_even_of_lt p.1 p.2 h_lt
    rwa [CharP.cast_eq_zero_iff,Nat.dvd_iff_mod_eq_zero]
  rw [h_zero, add_zero] at ha2
  have h_exists : ∃ p ∈ ((V N).filter (fun p => I_map N p = p)).filter (fun p => p.1 = p.2), (T N p : ZMod 2) ≠ 0 := by
    refine Finset.exists_ne_zero_of_sum_ne_zero (ha2▸ (by decide))
  rcases h_exists with ⟨p, hp_mem, _⟩
  have hp_V : p ∈ V N := by exact ( Finset.filter_subset _ _ ↑( Finset.filter_subset _ _ hp_mem) )
  have hI : I_map N p = p := by exact ( Finset.mem_filter.mp ↑( Finset.filter_subset _ _ hp_mem) ).right
  have hk : p.1 = p.2 := by exact ( Finset.mem_filter.1 hp_mem).2
  use p.1
  exact fixed_point_imp N p hp_V hI hk
  -- EVOLVE-BLOCK-END
