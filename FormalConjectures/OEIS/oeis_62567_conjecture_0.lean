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




open Nat Classical

/-- The number whose digits in base 10 are $n$'s digits reversed. -/
def reverse_nat (k : ℕ) : ℕ :=
  ofDigits 10 (digits 10 k).reverse

/--
A062567: First multiple of $n$ whose reverse is also divisible by $n$, or 0 if no such multiple exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- P(k) is the predicate for the multiplier k: k > 0 and n divides the reverse of (k*n).
    let P (k : ℕ) : Prop := k > 0 ∧ n ∣ reverse_nat (k * n)

    -- We check if a solution exists (using classical reasoning, since P is decidable).
    if h_ex : ∃ k, P k then
      -- Nat.find requires a DecidablePred instance, which holds for this property on ℕ.
      have HP : DecidablePred P := by infer_instance
      -- k_min is the smallest multiplier k >= 1.
      let k_min : ℕ := Nat.find h_ex
      k_min * n
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
def sum_digits : List ℕ → ℕ
| [] => 0
| d :: ds => d + sum_digits ds

def weight_digits : List ℕ → ℕ
| [] => 0
| _ :: ds => weight_digits ds + sum_digits ds

lemma sum_digits_append (A B : List ℕ) : sum_digits (A ++ B) = sum_digits A + sum_digits B := by
  induction A with{simp_all![sum_digits, add_assoc] }

lemma weight_digits_append (A B : List ℕ) : weight_digits (A ++ B) = weight_digits A + weight_digits B + A.length * sum_digits B := by
  norm_num[weight_digits, add_assoc]
  delta weight_digits
  use A.rec (by simp_all!) fun and R M=>?_
  simp_all[ add_assoc, add_mul,add_div, add_left_comm ↑(sum_digits R)]
  use R.rec (by norm_num[sum_digits]) (by simp_all[sum_digits, add_assoc])

lemma sum_digits_reverse (L : List ℕ) : sum_digits L.reverse = sum_digits L := by
  induction L with
  | nil => rfl
  | cons d ds ih =>
    have h1 : (d :: ds).reverse = ds.reverse ++ [d] := List.reverse_cons
    have h2 : sum_digits (ds.reverse ++ [d]) = sum_digits ds.reverse + sum_digits [d] := sum_digits_append ds.reverse [d]
    have h3 : sum_digits [d] = d := rfl
    have h4 : sum_digits (d :: ds) = d + sum_digits ds := rfl
    simp_all only[d.add_comm]

lemma weight_digits_reverse_add (L : List ℕ) : weight_digits L.reverse + weight_digits L = (L.length - 1) * sum_digits L := by
  induction L with
  | nil => rfl
  | cons d ds ih =>
    have h1 : (d :: ds).reverse = ds.reverse ++ [d] := List.reverse_cons
    have h2 : weight_digits (ds.reverse ++ [d]) = weight_digits ds.reverse + weight_digits [d] + ds.reverse.length * sum_digits [d] := weight_digits_append ds.reverse [d]
    have h3 : weight_digits [d] = 0 := rfl
    have h4 : sum_digits [d] = d := rfl
    have h5 : ds.reverse.length = ds.length := List.length_reverse
    have h6 : weight_digits (d :: ds) = weight_digits ds + sum_digits ds := rfl
    have h7 : sum_digits (d :: ds) = d + sum_digits ds := rfl
    have h8 : (d :: ds).length - 1 = ds.length := rfl
    use h1▸h2▸h5.symm▸h6▸h4.symm▸h8.symm▸h7▸by if a:ds.length=0 then simp_all! else linear_combination ih+.add_sub_of_le (pos_of_ne_zero a) *sum_digits ds+h3

lemma ofDigits_mod_81 (L : List ℕ) : ofDigits 10 L % 81 = (sum_digits L + 9 * weight_digits L) % 81 := by
  refine L.rec rfl fun and K V =>Nat.ofDigits_cons▸.symm ↑(.trans (by rw [weight_digits,sum_digits]) ? _)
  exact (81).modEq_of_dvd (by valid)

lemma gcd_81 (m : ℕ) : Nat.gcd (2 + 9 * m) 81 = 1 := by
  exact (Nat.prime_three.coprime_iff_not_dvd.2 (by valid)).symm.pow_right 4

lemma coprime_mod_81 (m S : ℕ) (h : (2 + 9 * m) * S % 81 = 0) : S % 81 = 0 := by
  apply(((Nat.prime_three.coprime_iff_not_dvd.mpr (by valid)).pow_left @4).dvd_mul_left.1 ↑(Nat.dvd_of_mod_eq_zero h)).modEq_zero_nat

-- Helper lemmas for finite cases
lemma digits_lt_10 (x : ℕ) (d : ℕ) (h : d ∈ digits 10 x) : d ≤ 9 := by
  exact (Nat.digits_lt_base' (h)).le_pred

lemma sum_digits_bound (L : List ℕ) (h_all : ∀ d ∈ L, d ≤ 9) : sum_digits L ≤ 9 * L.length := by
  use L.rec (by decide) ?_ h_all
  exact (fun R M a s=>.trans (by cases R with cases M with norm_num[sum_digits,Nat.digit_sum_le]) ((Nat.add_le_add (s R (by constructor)) ( a fun and=>s and ∘M.mem_cons_of_mem R)).trans_eq (add_comm _ _)))

lemma length_digits_le (x : ℕ) (h : x < 10^9) : (digits 10 x).length ≤ 9 := by
  if R :x = 0 then{bound} else {exact(10).digits_len x (by decide) (R)▸Nat.log_lt_of_lt_pow R h}

lemma ofDigits_of_all_9 (L : List ℕ) (h_len : L.length ≤ 9) (h_all : ∀ d ∈ L, d ≤ 9) (h_sum : sum_digits L ≥ 81) : ofDigits 10 L = 999999999 := by
  cases h_len.eq_or_lt.symm
  · delta sum_digits at*
    rcases(h_sum.trans (.trans (ge_of_eq (by exact L.rec (by decide) (by simp_all!) h_all)) ( L.sum_le_card_nsmul 9 h_all))).not_gt (by valid:_*9< _)
  delta sum_digits at*
  use match L with|[x,y,z,l,a,b,i,A, B] =>show x+10*(y+10*(z+10*(l+10*(a+10*(b+10*(i+10* (A+10* B)))))))=999999999 from (by_contra fun and=>(h_sum.not_gt) ? _)
  norm_num at h_all⊢
  omega

lemma x_lt_10_pow_9 (x : ℕ) (h : x < 10^9 - 1) : x < 999999999 := by
  valid
lemma a_9 : a 9 = 9 := by
  push_cast[a]
  norm_num +decide [reverse_nat,Exists.intro (1 : ℕ),Nat.find_eq_iff]

lemma a_27 : a 27 = 999 := by
  delta a
  norm_num+decide[reverse_nat,Exists.intro true,((Nat.find_eq_iff _).2 _:.find _=27)]
  norm_num only [Nat.digits, dif_pos, false,Exists.intro (@999/27)]
  unfold Nat.digitsAux List.reverse Nat.digitsAux Nat.digitsAux Nat.digitsAux
  norm_num+decide[Exists.intro (999/27),((congr_arg₂ _) ↑_ rfl ).trans (Nat.div_mul_cancel (by decide:27 ∣999)),Nat.find_eq_iff]

lemma no_solution_81 (k : ℕ) (h_k : k > 0) (h_lt : k < 12345679) : ¬ (81 ∣ reverse_nat (k * 81)) := by
  intro h_rev
  let x := k * 81
  have hx_pos : x > 0 := by bound
  have hx_lt : x < 10^9 - 1 := by omega
  have hx_mod : x % 81 = 0 := by apply k.mul_mod_left
  let L := digits 10 x
  have h_val : ofDigits 10 L = x := Nat.ofDigits_digits 10 x
  have h_rev_val : ofDigits 10 L.reverse = reverse_nat x := rfl
  have h1 : ofDigits 10 L % 81 = (sum_digits L + 9 * weight_digits L) % 81 := ofDigits_mod_81 L
  have h2 : ofDigits 10 L.reverse % 81 = (sum_digits L.reverse + 9 * weight_digits L.reverse) % 81 := ofDigits_mod_81 L.reverse
  have h3 : sum_digits L.reverse = sum_digits L := sum_digits_reverse L
  have h4 : weight_digits L.reverse + weight_digits L = (L.length - 1) * sum_digits L := weight_digits_reverse_add L
  have h_rev_mod : reverse_nat x % 81 = 0 := by exact (h_rev).modEq_zero_nat
  have h_sum1 : (sum_digits L + 9 * weight_digits L) % 81 = 0 := by rwa[<-h1,h_val]
  have h_sum2 : (sum_digits L + 9 * weight_digits L.reverse) % 81 = 0 := by simp_all only
  have h_add : ((sum_digits L + 9 * weight_digits L) + (sum_digits L + 9 * weight_digits L.reverse)) % 81 = 0 := by push_cast [*, false,Nat.add_mod]
  have h_add2 : (2 * sum_digits L + 9 * (L.length - 1) * sum_digits L) % 81 = 0 := by refine h_add▸congr_arg (·%81) (by·linear_combination-h4*9)
  have h_add3 : (2 + 9 * (L.length - 1)) * sum_digits L % 81 = 0 := by rwa [ add_mul]
  have h_S_mod : sum_digits L % 81 = 0 := coprime_mod_81 (L.length - 1) (sum_digits L) h_add3
  have h_S_pos : sum_digits L > 0 := by norm_num[sum_digits,pos_iff_ne_zero]
                                        delta sum_digits
                                        exact (hx_pos).ne' ∘(h_val▸ L.rec (by decide) (by simp_all!))
  have h_S_ge : sum_digits L ≥ 81 := by exact (81).le_of_dvd h_S_pos<|Nat.dvd_of_mod_eq_zero h_S_mod
  have hL_all : ∀ d ∈ L, d ≤ 9 := digits_lt_10 x
  have h_x_lt_pow : x < 10^9 := by exact (hx_lt.trans (by decide) )
  have hL_len : L.length ≤ 9 := length_digits_le x h_x_lt_pow
  have hx_eq : ofDigits 10 L = 999999999 := ofDigits_of_all_9 L hL_len hL_all h_S_ge
  have h_x_eq2 : x = 999999999 := by convert←hx_eq
  have h_x_lt_val : x < 999999999 := x_lt_10_pow_9 x hx_lt
  apply (by assumption :).ne (by valid)

lemma a_eq_of_min (n k : ℕ) (hn : n > 0) (hk : k > 0 ∧ n ∣ reverse_nat (k * n))
  (hmin : ∀ j, 0 < j → j < k → ¬ (n ∣ reverse_nat (j * n))) :
  a n = k * n := by
  push_cast[a,reverse_nat,.>·]at*
  rw[dif_pos ⟨k,hk⟩,Nat.find_eq_iff _|>.2 ⟨hk,by tauto⟩,if_neg hn.ne']

lemma a_81_k : a 81 = 12345679 * 81 := by
  have hn : 81 > 0 := by decide
  have hk_pos : 12345679 > 0 := by decide
  have hk_div : 81 ∣ reverse_nat (12345679 * 81) := by norm_num only[reverse_nat]
                                                       norm_num +decide
  have hk : 12345679 > 0 ∧ 81 ∣ reverse_nat (12345679 * 81) := And.intro hk_pos hk_div
  have hmin : ∀ j, 0 < j → j < 12345679 → ¬ (81 ∣ reverse_nat (j * 81)) := by
    intro j hj1 hj2
    exact no_solution_81 j hj1 hj2
  exact a_eq_of_min 81 12345679 hn hk hmin

lemma a_81 : a 81 = 999999999 := by
  have h := a_81_k
  have h_eq : 12345679 * 81 = 999999999 := by rfl
  rw [h_eq] at h
  exact h

def L5 : List ℕ := [2, 9, 7, 9, 9, 9, 9, 9, 7, 9, 2]

def L_seq : ℕ → List ℕ
  | 0 => L5
  | (k+1) => L_seq k ++ L_seq k ++ L_seq k

def V (k : ℕ) : ℕ := ofDigits 10 (L_seq k)

lemma L_seq_len (k : ℕ) : (L_seq k).length = 11 * 3^k := by
  delta L_seq
  induction k with|zero =>constructor|succ and a=>exact (.trans (by rw [List.length_append,List.length_append, a]) (by ring ) )

lemma V_step (k : ℕ) : V (k+1) = V k * (1 + 10^(11 * 3^k) + 10^(22 * 3^k)) := by
  rewrite [add_assoc, V]
  delta V L_seq
  norm_num [Nat.ofDigits_append, mul_add]
  simp_all![←two_mul,mul_comm (Nat.ofDigits _ _),←mul_assoc,←pow_add]
  exact (congr_arg₂ _) ((congr_arg (10^ · * _) (by induction (k : ℕ) with | zero=> constructor |succ and a=>exact (.trans (by rw [List.length_append,List.length_append, a]) (by(ring)))))) ((congr_arg (10 ^· * _) (by (induction (k : ℕ) with|zero=> constructor |succ and a=>grind))))

lemma three_div_factor (L : ℕ) : 3 ∣ 1 + 10^L + 10^(2*L) := by
  push_cast [Nat.add_mod,Nat.pow_mod, one_pow,Nat.dvd_iff_mod_eq_zero]

lemma V_div (k : ℕ) : 3^(5+k) ∣ V k := by
  rw [←add_comm, V]
  delta and L_seq
  refine k.rec (by decide) fun and ⟨a, _⟩ =>pow_succ (3) @_▸?_
  norm_num only[ *, mul_dvd_mul_left, ←one_add_mul, ← add_mul,dvd_mul_of_dvd_left,Nat.ofDigits_append]
  exact (3).mul_comm _▸mul_dvd_mul ((3).dvd_of_mod_eq_zero (by push_cast[Nat.add_mod, one_pow,Nat.pow_mod])) ⟨a, rfl⟩

lemma V_rev (k : ℕ) : reverse_nat (V k) = V k := by
  delta reverse_nat V
  delta L_seq
  let g : ℕ →List ℕ:=Nat.rec L5 fun and true => true++true++true
  trans .ofDigits 10 ((10:).digits (.ofDigits 10 (g k))).reverse
  · exact (congr_arg _) ((congr_arg _).comp (congr_arg _) ((congr_arg _) @(k.rec rfl fun and=>congr_arg fun and=>and++and++ and)))
  rw[Nat.digits_ofDigits 10 (by decide)]
  · exact (congr_arg _) @(k.rec ↑rfl (by (aesop)))
  · induction k with simp_all+decide[g, or_imp]
  · induction k with simp_all[g,L5]

lemma V_pos (k : ℕ) : V k > 0 := by
  refine k.strongRec fun and(a) => match and with|0|(1) | S+2=>?_
  · hint
  · simp_all!
    show 0<star _
    focus decide
  simp_all! -contextual[Nat.forall_lt_succ, add_pos]
  delta V
  delta L_seq
  exact(S+2).rec (by decide) (by simp_all[Nat.ofDigits_append])

lemma V_lt (k : ℕ) : V k < 10^(3^(k+3)) - 1 := by
  simp_rw [ Nat.lt_sub_iff_add_lt, V]
  delta and L_seq
  refine k.rec (by decide) fun and x =>(lt_of_le_of_lt (Nat.ofDigits_lt_base_pow_length' (and.rec (by decide) (by simp_all))) ((pow_mul 10 (3^ _) _)▸?_))
  exact (Nat.pow_lt_pow_right (by decide) ↑(and.rec (by decide) fun and x =>lt_of_le_of_lt (by rw [List.length_append,List.length_append]) (by grind))).trans_eq (pow_mul _ _ _)

lemma a_le_V (k : ℕ) : a (3^(5+k)) ≤ V k := by
  norm_num[a, false,add_comm, V]
  delta reverse_nat and L_seq
  trans .ofDigits 10 ↑(k.recOn L5 fun and true => true++true++true)
  · refine if a: (_) then(dif_pos a▸(Nat.mul_le_of_le_div _ _ _ ∘Nat.find_min' a) ? _)else(dif_neg a▸bot_le)
    rewrite [Nat.div_mul_cancel,Nat.digits_ofDigits 10 (by decide)]
    · replace a: (3: ℕ) ^(k +5) ∣.ofDigits 10 @(k.rec L5 fun and true => true++true++true :List ℕ).reverse:= k.rec (by decide) fun and ⟨a, _⟩=>pow_succ (3) ↑( _)▸?_
      · simp_all only[Nat.ofDigits_append,List.reverse_append]
        norm_num[←one_add_mul,←add_mul,←mul_assoc, mul_dvd_mul.comp (3).dvd_of_mod_eq_zero,mul_comm (3^ _),Nat.add_mod,Nat.mul_mod,Nat.pow_mod]
      use Nat.div_pos (k.rec (by decide) (fun A B=>pow_succ (3) _▸?_)) (Nat.pow_pos (by decide))
      norm_num[mul_comm (3^ _),Nat.ofDigits_append, mul_le_mul',le_add_left, B]
      norm_num[B,Nat.succ_mul,←add_assoc, mul_le_mul',Nat.succ_le]
      exact (add_comm _ _).le.trans (Nat.add_le_add (by simp_rw [ ←List.append_assoc, B]) (le_mul_of_one_le_of_le (by bound) (Nat.add_le_add (by simp_rw [ ←List.append_assoc, B]) (B.trans (by norm_num[Nat.le_mul_of_pos_left _ _])))))
    · use k.rec (by decide) (by norm_num)
    · exact k.rec (by decide) (by simp_all!)
    · refine k.rec (by decide) fun and ⟨a, _⟩ =>pow_succ (3) ↑_▸?_
      push_cast[*, true,Nat.ofDigits_append]
      norm_num[mul_comm (3^ _),←one_add_mul,←add_mul,(3).dvd_iff_mod_eq_zero, mul_dvd_mul _,Nat.add_mod,Nat.pow_mod]
  · exact (congr_arg _ ↑(k.rec rfl<|by simp_all)).le

-- Helper lemma for the general inequality when n >= 5
lemma a_gt_4 (n : ℕ) (hn : 5 ≤ n) : a (3 ^ n) < 10 ^ 3 ^ (n - 2) - 1 := by
  have h_n : n = 5 + (n - 5) := by omega
  have h_n2 : n - 2 = (n - 5) + 3 := by refine(n).sub_eq_of_eq_add (by valid)
  have h1 : a (3 ^ (5 + (n - 5))) ≤ V (n - 5) := a_le_V (n - 5)
  have h2 : V (n - 5) < 10 ^ 3 ^ ((n - 5) + 3) - 1 := V_lt (n - 5)
  have h3 : a (3 ^ n) ≤ V (n - 5) := by convert h1
  have h4 : V (n - 5) < 10 ^ 3 ^ (n - 2) - 1 := by rwa[h_n2]
  exact (h3).trans_lt (h4)
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (n : ℕ) : 2 ≤ n → (a (3 ^ n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) := by
  -- EVOLVE-BLOCK-START
  intro hn
  constructor
  · intro h
    rcases lt_trichotomy n 5 with h_lt | rfl | h_gt
    · omega
    · have h5 := a_gt_4 5 (by omega)
      linarith
    · have hgt := a_gt_4 n (by omega)
      linarith
  · rintro (rfl | rfl | rfl)
    · exact a_9
    · exact a_27
    · exact a_81
  -- EVOLVE-BLOCK-END
