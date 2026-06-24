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




open List Finset Nat

/--
A306424: Numbers $k$ such that the base $b$ expansion of $k$ for each $b = 3..k-1$ never contains more than two distinct digits.
-/
def A306424_condition (k : ℕ) : Prop :=
  -- The bases $b$ range over $3 \le b \le k-1$, expressed as $3 \le b$ and $b < k$.
  ∀ b : ℕ, 3 ≤ b ∧ b < k → ((Nat.digits b k).toFinset.card) ≤ 2

/--
The sequence A306424: Numbers $k$ such that the base $b$ expansion of $k$ for each $b = 3..k-1$ never contains more than two distinct digits.
-/
noncomputable def a (n : ℕ) : ℕ := n.nth A306424_condition

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
def my_digits (fuel b k : ℕ) : List ℕ :=
  match fuel with
  | 0 => []
  | f + 1 =>
    if k = 0 then []
    else (k % b) :: my_digits f b (k / b)

def count_distinct (l : List ℕ) : ℕ :=
  l.eraseDups.length

def check_cond (k : ℕ) : Bool :=
  (List.range k).all fun b =>
    if b < 3 then true
    else
      (count_distinct (my_digits (k + 1) b k)) ≤ 2

def all_fail (k max : ℕ) : Bool :=
  match max with
  | 0 => true
  | m + 1 =>
    if check_cond k then false
    else all_fail (k + 1) m

set_option maxRecDepth 1000000
lemma all_fail_44_288 : all_fail 44 245 = true := by decide

lemma my_digits_eq_fuel (fuel k b : ℕ) (hb : 2 ≤ b) (h_fuel : k < fuel) : my_digits fuel b k = Nat.digits b k := by
  delta Nat.digits my_digits
  induction (by bound: ℕ) generalizing k with|zero=>contradiction|succ=>_
  match b with | S+2=>cases k with·simp_all [Nat.digitsAux,↑(Nat.le_of_lt_succ (by assumption)).trans_lt' ∘Nat.div_lt_self _,id]

lemma my_digits_eq (k b : ℕ) (hb : 2 ≤ b) : my_digits (k + 1) b k = Nat.digits b k := by
  delta my_digits
  induction k using Nat.strongRec
  obtain ⟨rfl⟩ :=eq_or_ne (by valid) 0
  · exact (b.digits_zero.symm)▸rfl
  cases h:by valid/b
  · norm_num[b.digits_def' hb,@pos_iff_ne_zero ℕ, *]
    cases‹ℕ› with constructor
  push_cast [eq_self,b.digits_def' hb,pos_of_ne_zero (by assumption), h▸Nat.div_lt_self _ hb, *]
  revert‹ℕ›b
  use fun and R M a s=>congr_arg _ (( (by bound: ℕ):).strongRec ?_ (a+1) (s.symm.trans_lt (Nat.div_lt_self (by valid) R)))
  exact (fun a s A B=>match a with | S+1=>match A with|0=>and.digits_zero.symm|n + 1=>and.digits_def' R n.succ_pos▸congr_arg _ (s S (by constructor) (_) (Nat.div_lt_self n.succ_pos R|>.trans_le B.le_pred)))

lemma count_distinct_eq (l : List ℕ) : count_distinct l = l.toFinset.card := by
  norm_num[count_distinct]
  refine l.reverseRecOn rfl fun and I I=>.trans (by rw [List.eraseDups_append,List.length_append]) ((symm) ? _)
  cases em (by assumption ∈ and) with ·simp_all [List.removeAll, true,List.eraseDups_cons]

lemma check_cond_imp (k : ℕ) (hk : A306424_condition k) : check_cond k = true := by
  revert k
  show∀ (x _),(id _) = _
  conv_rhs=>norm_num[count_distinct, A306424_condition, true,Nat.lt_succ]
  use fun and K V H=>or_iff_not_imp_left.2 fun and' =>.trans ( show(List.eraseDups (id _) :List ℕ).length≤_ from(?_)) (K V (by valid) (H))
  norm_num[my_digits, V.digits_def' (by valid) H.pos, H.pos.ne',List.eraseDups_cons]
  convert_to ((my_digits and V (and/V)).filter (!· ==and%V)).toFinset.card<_
  · refine(List.filter _ _).reverseRecOn rfl fun and a s=>.trans (by rw [List.eraseDups_append]) ?_
    cases@em (a ∈and) with norm_num[*,List.removeAll,List.eraseDups_cons]
  delta my_digits
  use Finset.card_lt_card ⟨fun a s=>? _,by norm_num ∘(@. (and%V) )⟩
  use Finset.mem_insert_of_mem (by_contra fun andM=>absurd (List.mem_filter.1.comp (List.mem_toFinset.1) s).1 (and.rec (nofun) ?_ (and/V) andM))
  use fun and A B p=>match B with|0=>nofun | S+1=>List.mem_cons.not.2 (not_or_intro (p ∘ (by norm_num[., V.digits_def' (by valid)])) ( (A _) (p ∘by norm_num+contextual[V.digits_def' (by valid)])))

lemma all_fail_imp {k max n : ℕ} (h : all_fail k max = true) (hn1 : k ≤ n) (hn2 : n < k + max) : check_cond n = false := by
  delta all_fail at *
  induction max generalizing k (n : ℕ) with |zero=>omega|succ=>grind

lemma check_cond_eq (k : ℕ) : A306424_condition k ↔ check_cond k = true := by
  show(A306424_condition k) ↔(id _) = true
  simp_all(config := {singlePass:=1}) -contextual[count_distinct, A306424_condition, false,Nat.lt_succ_iff]
  show @_ ↔∀ (x _),_ ∨List.length (List.eraseDups (id _)) ≤2
  delta my_digits id
  refine(forall_congr') fun and=> if a:_ then (if_neg a▸? _)else by valid
  norm_num[Nat.succ_le, or_iff_not_imp_left]
  refine(forall_comm.trans (forall₂_congr fun A B=>iff_of_eq ((congr_arg₂ _) (and.digits_def' B.le ((pos_of_ne_zero a))▸symm ? _) rfl)))
  trans(k%and::and.digits ↑( k /and)).eraseDups.length
  · congr 3
    use k.strongRec ?_ (k/ _)<|k.div_lt_self A.pos B.le
    use fun and(a) R M=>match and with | S+1=>match R with|0=>by norm_num|n + 1=>((congr_arg _) (a S (by constructor) ( _) ((Nat.div_lt_self n.succ_pos B.le).trans_le M.le_pred))).trans (Nat.digits_def' B.le n.succ_pos).symm
  · refine(_::_).reverseRecOn rfl fun and R M=>.trans (by rw [List.eraseDups_append]) ?_
    cases em (R ∈and) with norm_num[*,List.removeAll,List.eraseDups_cons]

lemma k_43 : check_cond 43 = true := by rfl

lemma base_fail {k c x y z : ℕ}
  (hc : 3 ≤ c) (hx : 0 < x) (hxc : x < c) (hyc : y < c) (hzc : z < c)
  (hk : k = x * c^2 + y * c + z)
  (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
  ¬ A306424_condition k := by
  simp_rw [hk, A306424_condition] at*
  apply mt (· c ⟨hc,by nlinarith⟩)
  simp_all[c.mul_add_div,mul_comm y,mul_left_comm x,add_assoc,c.digits_def',hx.trans,Nat.mod_eq_of_lt,Nat.div_eq_of_lt,sq,ne_comm,hxc.pos]
  simp_all[c.mul_add_div (by valid),c.digits_def' (by valid),mul_comm x,Nat.mod_eq_of_lt,Nat.div_eq_of_lt,ne_comm,hxc.pos]

lemma find_failing_base (k b : ℕ) (hb1 : b^2 ≤ k) (hb2 : k < (b+1)^2) (hb3 : 17 ≤ b) :
  ∃ c x y z : ℕ, 3 ≤ c ∧ 0 < x ∧ x < c ∧ y < c ∧ z < c ∧ k = x * c^2 + y * c + z ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z := by
  have hb2_exp : k < b^2 + 2 * b + 1 := by
    calc k < (b+1)^2 := hb2
         _ = b^2 + 2 * b + 1 := by ring
  set r := k - b^2
  have hk_eq : k = b^2 + r := by omega
  have hr_bound : r ≤ 2 * b := by omega

  if h0 : r = 0 then
    have heq : k = 1 * (b - 3) ^ 2 + 6 * (b - 3) + 9 := by
      apply Int.ofNat_inj.mp
      have hh1 : (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := by exact_mod_cast hk_eq
      have h2 : (r : ℤ) = 0 := by omega
      have h3 : ((b - 3 : ℕ) : ℤ) = (b : ℤ) - 3 := by omega
      calc (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := hh1
           _       = 1 * ((b : ℤ) - 3)^2 + 6 * ((b : ℤ) - 3) + 9 := by rw [h2]; ring
           _       = 1 * ((b - 3 : ℕ) : ℤ)^2 + 6 * ((b - 3 : ℕ) : ℤ) + 9 := by rw [h3]
    exact ⟨b - 3, 1, 6, 9, by omega, by omega, by omega, by omega, by omega, heq, by omega, by omega, by omega⟩
  else if h1 : r = 1 then
    have heq : k = 1 * (b - 2) ^ 2 + 4 * (b - 2) + 5 := by
      apply Int.ofNat_inj.mp
      have hh1 : (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := by exact_mod_cast hk_eq
      have h2 : (r : ℤ) = 1 := by omega
      have h3 : ((b - 2 : ℕ) : ℤ) = (b : ℤ) - 2 := by omega
      calc (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := hh1
           _       = 1 * ((b : ℤ) - 2)^2 + 4 * ((b : ℤ) - 2) + 5 := by rw [h2]; ring
           _       = 1 * ((b - 2 : ℕ) : ℤ)^2 + 4 * ((b - 2 : ℕ) : ℤ) + 5 := by rw [h3]
    exact ⟨b - 2, 1, 4, 5, by omega, by omega, by omega, by omega, by omega, heq, by omega, by omega, by omega⟩
  else if h2 : r < b then
    have heq : k = 1 * b ^ 2 + 0 * b + r := by
      apply Int.ofNat_inj.mp
      have hh1 : (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := by exact_mod_cast hk_eq
      calc (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := hh1
           _       = 1 * (b : ℤ)^2 + 0 * (b : ℤ) + (r : ℤ) := by ring
    exact ⟨b, 1, 0, r, by omega, by omega, by omega, by omega, by omega, heq, by omega, by omega, by omega⟩
  else if h3 : r = b then
    have heq : k = 1 * (b - 1) ^ 2 + 3 * (b - 1) + 2 := by
      apply Int.ofNat_inj.mp
      have hh1 : (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := by exact_mod_cast hk_eq
      have h2 : (r : ℤ) = (b : ℤ) := by omega
      have hh3 : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
      calc (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := hh1
           _       = 1 * ((b : ℤ) - 1)^2 + 3 * ((b : ℤ) - 1) + 2 := by rw [h2]; ring
           _       = 1 * ((b - 1 : ℕ) : ℤ)^2 + 3 * ((b - 1 : ℕ) : ℤ) + 2 := by rw [hh3]
    exact ⟨b - 1, 1, 3, 2, by omega, by omega, by omega, by omega, by omega, heq, by omega, by omega, by omega⟩
  else if h4 : r = b + 1 then
    have heq : k = 1 * (b - 2) ^ 2 + 5 * (b - 2) + 7 := by
      apply Int.ofNat_inj.mp
      have hh1 : (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := by exact_mod_cast hk_eq
      have h2 : (r : ℤ) = (b : ℤ) + 1 := by omega
      have h3 : ((b - 2 : ℕ) : ℤ) = (b : ℤ) - 2 := by omega
      calc (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := hh1
           _       = 1 * ((b : ℤ) - 2)^2 + 5 * ((b : ℤ) - 2) + 7 := by rw [h2]; ring
           _       = 1 * ((b - 2 : ℕ) : ℤ)^2 + 5 * ((b - 2 : ℕ) : ℤ) + 7 := by rw [h3]
    exact ⟨b - 2, 1, 5, 7, by omega, by omega, by omega, by omega, by omega, heq, by omega, by omega, by omega⟩
  else if h5 : r ≤ 2 * b - 4 then
    have heq : k = 1 * (b - 1) ^ 2 + 3 * (b - 1) + (r - b + 2) := by
      apply Int.ofNat_inj.mp
      have hh1 : (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := by exact_mod_cast hk_eq
      have h3 : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
      have h4 : ((r - b + 2 : ℕ) : ℤ) = (r : ℤ) - (b : ℤ) + 2 := by omega
      calc (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := hh1
           _       = 1 * ((b : ℤ) - 1)^2 + 3 * ((b : ℤ) - 1) + ((r : ℤ) - (b : ℤ) + 2) := by ring
           _       = 1 * ((b - 1 : ℕ) : ℤ)^2 + 3 * ((b - 1 : ℕ) : ℤ) + ((r - b + 2 : ℕ) : ℤ) := by rw [h3, h4]
    exact ⟨b - 1, 1, 3, r - b + 2, by omega, by omega, by omega, by omega, by omega, heq, by omega, by omega, by omega⟩
  else if h6 : r = 2 * b - 3 then
    have heq : k = 1 * (b - 1) ^ 2 + 4 * (b - 1) + 0 := by
      apply Int.ofNat_inj.mp
      have hh1 : (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := by exact_mod_cast hk_eq
      have h2 : (r : ℤ) = 2 * (b : ℤ) - 3 := by omega
      have h3 : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
      calc (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := hh1
           _       = 1 * ((b : ℤ) - 1)^2 + 4 * ((b : ℤ) - 1) + 0 := by rw [h2]; ring
           _       = 1 * ((b - 1 : ℕ) : ℤ)^2 + 4 * ((b - 1 : ℕ) : ℤ) + 0 := by rw [h3]
    exact ⟨b - 1, 1, 4, 0, by omega, by omega, by omega, by omega, by omega, heq, by omega, by omega, by omega⟩
  else if h7 : r = 2 * b - 2 then
    have heq : k = 1 * (b - 3) ^ 2 + 8 * (b - 3) + 13 := by
      apply Int.ofNat_inj.mp
      have hh1 : (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := by exact_mod_cast hk_eq
      have h2 : (r : ℤ) = 2 * (b : ℤ) - 2 := by omega
      have h3 : ((b - 3 : ℕ) : ℤ) = (b : ℤ) - 3 := by omega
      calc (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := hh1
           _       = 1 * ((b : ℤ) - 3)^2 + 8 * ((b : ℤ) - 3) + 13 := by rw [h2]; ring
           _       = 1 * ((b - 3 : ℕ) : ℤ)^2 + 8 * ((b - 3 : ℕ) : ℤ) + 13 := by rw [h3]
    exact ⟨b - 3, 1, 8, 13, by omega, by omega, by omega, by omega, by omega, heq, by omega, by omega, by omega⟩
  else if h8 : r = 2 * b - 1 then
    have heq : k = 1 * (b - 1) ^ 2 + 4 * (b - 1) + 2 := by
      apply Int.ofNat_inj.mp
      have hh1 : (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := by exact_mod_cast hk_eq
      have h2 : (r : ℤ) = 2 * (b : ℤ) - 1 := by omega
      have h3 : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
      calc (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := hh1
           _       = 1 * ((b : ℤ) - 1)^2 + 4 * ((b : ℤ) - 1) + 2 := by rw [h2]; ring
           _       = 1 * ((b - 1 : ℕ) : ℤ)^2 + 4 * ((b - 1 : ℕ) : ℤ) + 2 := by rw [h3]
    exact ⟨b - 1, 1, 4, 2, by omega, by omega, by omega, by omega, by omega, heq, by omega, by omega, by omega⟩
  else
    have h9 : r = 2 * b := by omega
    have heq : k = 1 * b ^ 2 + 2 * b + 0 := by
      apply Int.ofNat_inj.mp
      have hh1 : (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := by exact_mod_cast hk_eq
      have h2 : (r : ℤ) = 2 * (b : ℤ) := by omega
      calc (k : ℤ) = (b : ℤ)^2 + (r : ℤ) := hh1
           _       = 1 * (b : ℤ)^2 + 2 * (b : ℤ) + 0 := by rw [h2]; ring
    exact ⟨b, 1, 2, 0, by omega, by omega, by omega, by omega, by omega, heq, by omega, by omega, by omega⟩

lemma big_fail (k : ℕ) (hk : 289 ≤ k) : ¬ A306424_condition k := by
  intro h
  have hb1 : k.sqrt^2 ≤ k := by apply(k).sqrt_le'
  have hb2 : k < (k.sqrt+1)^2 := by apply k.lt_succ_sqrt'
  have hb3 : 17 ≤ k.sqrt := by rwa [Nat.le_sqrt]
  have ⟨c, x, y, z, hc, hx, hxc, hyc, hzc, h_eq, hxy, hyz, hxz⟩ := find_failing_base k k.sqrt hb1 hb2 hb3
  exact base_fail hc hx hxc hyc hzc h_eq hxy hyz hxz h

-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : A306424_condition 43 ∧ ∀ k : ℕ, 43 < k → ¬A306424_condition k := by
  -- EVOLVE-BLOCK-START
  constructor
  · exact (check_cond_eq 43).mpr k_43
  · intro k hk
    by_cases h_bound : k ≤ 288
    · have h_fail : check_cond k = false := all_fail_imp all_fail_44_288 (by omega) (by omega)
      intro h_cond
      have h_true := (check_cond_eq k).mp h_cond
      rw [h_fail] at h_true
      contradiction
    · have h_big : 289 ≤ k := by omega
      exact big_fail k h_big
  -- EVOLVE-BLOCK-END
