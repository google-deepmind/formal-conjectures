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




open Nat Set

/--
A224515: $a(n) = \text{least } k \text{ such that } \sqrt{k^2 \operatorname{XOR} (k+1)^2} = 2n+1, \text{ } a(n) = -1 \text{ if there is no such } k$.
This is equivalent to finding the smallest $k \in \mathbb{N}$ such that $k^2 \oplus (k+1)^2 = (2n+1)^2$.
We use the set infimum ($\operatorname{sInf}$) to denote the least element of the set of natural numbers satisfying the condition.
Since Mathlib's `sInf` on a subset of `ℕ` gives a result in `ℕ`, this definition is only completely faithful to the OEIS when the set is non-empty.
The OEIS definition implies that the set of k's is non-empty for all n.
-/
noncomputable def A224515 (n : ℕ) : ℕ :=
  -- The term (2*n + 1)^2 is the target value.
  let target_sq : ℕ := (2 * n + 1) ^ 2
  -- Define the set of candidate k's.
  sInf { k : ℕ | Nat.xor (k ^ 2) ((k + 1) ^ 2) = target_sq }

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
lemma xor_eq_add_sub (a b : ℕ) : Nat.xor a b + 2 * Nat.land a b = a + b := by
  refine a.binaryRec (by simp_all[Nat.xor, true,Nat.land]) ?_ b
  refine fun and A B R=> R.binaryRec (by norm_num[Nat.xor,Nat.land]) ?_
  simp_all(config := {singlePass:=1}) -contextual[Nat.xor,Nat.land]
  induction and with repeat use fun and left=>.trans ( by aesop) (.symm (.trans ( by aesop) (by. (linear_combination-B and * ( (2))))))

lemma my_xor_cancel_left (a b : ℕ) : Nat.xor a (Nat.xor a b) = b := by
  apply @a.xor_cancel_left

lemma k_eq_M_implies_xor_eq_S (k M S : ℕ) (hS : S = 2 * M + 1) (hk : k + Nat.land (k ^ 2) S = M) :
    Nat.xor (k ^ 2) ((k + 1) ^ 2) = S := by
  have h1 : 2 * k + 2 * Nat.land (k ^ 2) S = 2 * M := by omega
  have h2 : 2 * k + 1 + 2 * Nat.land (k ^ 2) S = S := by omega
  have h3 : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
  have h4 : (k + 1) ^ 2 + 2 * Nat.land (k ^ 2) S = k ^ 2 + S := by omega
  have h5 : Nat.xor (k ^ 2) S + 2 * Nat.land (k ^ 2) S = k ^ 2 + S := xor_eq_add_sub (k ^ 2) S
  have h6 : (k + 1) ^ 2 = Nat.xor (k ^ 2) S := by omega
  rw [h6]
  exact my_xor_cancel_left (k^2) S

lemma xor_S_land_S (A S : ℕ) : Nat.land (Nat.xor A S) S = S - Nat.land A S := by
  use show Nat.land (A.xor _) S = S-A.land S from S.eq_sub_of_add_eq ( A.binaryRec (?_) ?_ S)
  · simp_all[Nat.land, true,Nat.xor]
    exact (·.binaryRec (by simp_all) (by simp_all))
  use fun and A B c=>c.binaryRec (by norm_num[Nat.land]) ?_
  simp_all(config := {singlePass:=1})-contextual[Nat.mul_add_div,Nat.xor,Nat.land]
  cases and with simp_all[←add_assoc, add_right_comm _ _ (2 * _),←mul_add]

lemma reverse_symmetry_z (z M S x : ℕ) (hS : S = 2 * M + 1) (hx_le : x ≤ S) (hz : z + 1 = x - M) (hx : x = Nat.land ((z + 1)^2) S) :
  Nat.land (z^2) S = S - x := by
  have h1 : 2 * x = S + 2 * z + 1 := by omega
  have h2 : (z + 1)^2 = z^2 + 2 * z + 1 := by ring
  have h3 : (z + 1)^2 + S = z^2 + 2 * x := by omega
  have h4 : Nat.xor ((z + 1)^2) S + 2 * x = (z + 1)^2 + S := by
    have h : Nat.xor ((z + 1)^2) S + 2 * Nat.land ((z + 1)^2) S = (z + 1)^2 + S := xor_eq_add_sub ((z + 1)^2) S
    omega
  have h5 : z^2 = Nat.xor ((z + 1)^2) S := by omega
  rw [h5]
  have h6 : Nat.land (Nat.xor ((z + 1)^2) S) S = S - x := by
    rw [xor_S_land_S ((z + 1)^2) S]
    exact congrArg (fun y => S - y) hx.symm
  exact h6

lemma sq_add_pow_mod (K m : ℕ) (hm : m ≥ 1) : ((K + 2^m)^2) % 2^(m+1) = (K^2) % 2^(m+1) := by
  match m with|i + 1=>exact (congr_arg (.% _) (by ring)).trans (Nat.mul_add_mod _ (K+2^i) _)

lemma land_mod_two_pow (A B m : ℕ) : Nat.land A B % 2^m = Nat.land (A % 2^m) (B % 2^m) := by
  apply A.and_mod_two_pow

lemma land_sq_add_pow_mod (K S m : ℕ) (hm : m ≥ 1) : Nat.land ((K + 2^m)^2) S % 2^(m+1) = Nat.land (K^2) S % 2^(m+1) := by
  rw [land_mod_two_pow, sq_add_pow_mod K m hm, ← land_mod_two_pow]

lemma mod_add_mod (a b c n : ℕ) (h : a % n = b % n) : (c + a) % n = (c + b) % n := by
  rwa[Nat.ModEq.add_left]

lemma construct_k_step (K S m : ℕ) (hm : m ≥ 1) : ((K + 2^m) + Nat.land ((K + 2^m)^2) S) % 2^(m+1) = (K + Nat.land (K^2) S + 2^m) % 2^(m+1) := by
  have h1 : ((K + 2^m) + Nat.land ((K + 2^m)^2) S) % 2^(m+1) = ((K + 2^m) + Nat.land (K^2) S) % 2^(m+1) :=
    mod_add_mod (Nat.land ((K + 2^m)^2) S) (Nat.land (K^2) S) (K + 2^m) (2^(m+1)) (land_sq_add_pow_mod K S m hm)
  have h2 : (K + 2^m) + Nat.land (K^2) S = K + Nat.land (K^2) S + 2^m := by omega
  rw [h1, h2]

def construct_k (S M : ℕ) : ℕ → ℕ
| 0 => 0
| (m + 1) =>
  let K := construct_k S M m
  if (K + Nat.land (K^2) S) % 2^(m+1) = M % 2^(m+1) then
    K
  else
    K + 2^m

lemma mod_fix_bit (A B m : ℕ) (h1 : A % 2^m = B % 2^m) (h2 : A % 2^(m+1) ≠ B % 2^(m+1)) :
  (A + 2^m) % 2^(m+1) = B % 2^(m+1) := by
  refine (Nat.ModEq.symm h1).dvd.elim fun and x =>(Nat.modEq_of_dvd (by_contra fun and' => h2 ((Nat.modEq_of_dvd) ?_)))
  exact (dvd_sub_comm.1 (x▸mul_dvd_mul_left _ (and.not_odd_iff_even.1 (and' ∘.rec (by use-1-.,show _-(A+2^m : ℤ)=2^(m+1)*( _)by cases. with grind))).two_dvd))

lemma construct_k_valid_zero (S M : ℕ) :
  (construct_k S M 0 + Nat.land (construct_k S M 0 ^ 2) S) % 2^0 = M % 2^0 := by
  grind

lemma construct_k_valid_one (S M : ℕ) (hM : M % 4 = 0) :
  (construct_k S M 1 + Nat.land (construct_k S M 1 ^ 2) S) % 2^1 = M % 2^1 := by
  norm_num[construct_k, false, (by valid : M % 2 =0),Nat.add_mod, true,Nat.land]

lemma construct_k_valid_step (S M m : ℕ) (hm : m ≥ 1) (ih : (construct_k S M m + Nat.land (construct_k S M m ^ 2) S) % 2^m = M % 2^m) :
  (construct_k S M (m + 1) + Nat.land (construct_k S M (m + 1) ^ 2) S) % 2^(m+1) = M % 2^(m+1) := by
  let K := construct_k S M m
  have hK : construct_k S M (m + 1) = if (K + Nat.land (K^2) S) % 2^(m+1) = M % 2^(m+1) then K else K + 2^m := rfl
  by_cases hc : (K + Nat.land (K^2) S) % 2^(m+1) = M % 2^(m+1)
  · rw [hK, if_pos hc]
    exact hc
  · rw [hK, if_neg hc]
    have h1 : ((K + 2^m) + Nat.land ((K + 2^m)^2) S) % 2^(m+1) = (K + Nat.land (K^2) S + 2^m) % 2^(m+1) := construct_k_step K S m hm
    rw [h1]
    exact mod_fix_bit (K + Nat.land (K^2) S) M m ih hc

lemma construct_k_valid (S M m : ℕ) (hM : M % 4 = 0) :
  (construct_k S M m + Nat.land (construct_k S M m ^ 2) S) % 2^m = M % 2^m := by
  induction m with
  | zero =>
    exact construct_k_valid_zero S M
  | succ m ih =>
    by_cases hm : m = 0
    · rw [hm]
      exact construct_k_valid_one S M hM
    · have hm1 : m ≥ 1 := by omega
      exact construct_k_valid_step S M m hm1 ih

def abs_diff (a b : ℕ) : ℕ := if a ≤ b then b - a else a - b

lemma land_le_right (a b : ℕ) : Nat.land a b ≤ b := by
  exact (a.and_le_right)

lemma mod_eq_of_lt (a b m : ℕ) (h1 : a % 2^m = b % 2^m) (h2 : a < 2^m) (h3 : b < 2^m) : a = b := by
  simp_all only[Nat.mod_eq_of_lt]

lemma K_eq_M_sub_d_mod (K M m d : ℕ) (hd : d < 2^m) (h : (K + d) % 2^m = M % 2^m) :
  K % 2^m = (M + 2^m - d) % 2^m := by
  exact (Nat.ModEq.add_right_cancel' _) ↑(h.trans (Nat.sub_add_cancel.comp (le_add_left) hd.le▸M.add_mod_right _).symm)

lemma sq_mod_eq_of_mod_eq (A B m : ℕ) (h : A % 2^m = B % 2^m) :
  A^2 % 2^m = B^2 % 2^m := by
  exact (Nat.ModEq.pow _) h

lemma land_mod_eq_of_mod_eq (A B S m : ℕ) (h : A % 2^m = B % 2^m) :
  Nat.land A S % 2^m = Nat.land B S % 2^m := by
  rw [land_mod_two_pow A S m, h, ← land_mod_two_pow B S m]

lemma abs_diff_sq_mod (M x m : ℕ) (hx : x < 2^m) :
  ((M + 2^m - x)^2) % 2^m = (abs_diff x M)^2 % 2^m := by
  simp_all -contextual[abs_sub_comm,<-ZMod.val_natCast,le_add_left hx.le,abs_diff]
  exact (congr_arg _) ((em _).elim (if_pos ·▸by simp_all only[Nat.cast_sub]) (if_neg ·▸by simp_all only[Nat.cast_sub, sub_sq_comm,le_of_lt, not_le]))

lemma exact_fixed_point_x (M S m K : ℕ) (hm : S < 2^m)
  (hK : (K + Nat.land (K^2) S) % 2^m = M % 2^m) :
  Nat.land (K^2) S = Nat.land ((abs_diff (Nat.land (K^2) S) M)^2) S := by
  let x := Nat.land (K^2) S
  have hx_le : x ≤ S := land_le_right (K^2) S
  have hx_lt : x < 2^m := by omega
  have h1 : K % 2^m = (M + 2^m - x) % 2^m := K_eq_M_sub_d_mod K M m x hx_lt hK
  have h2 : K^2 % 2^m = (M + 2^m - x)^2 % 2^m := sq_mod_eq_of_mod_eq K (M + 2^m - x) m h1
  have h3 : (M + 2^m - x)^2 % 2^m = (abs_diff x M)^2 % 2^m := abs_diff_sq_mod M x m hx_lt
  have h4 : K^2 % 2^m = (abs_diff x M)^2 % 2^m := by omega
  have h5 : Nat.land (K^2) S % 2^m = Nat.land ((abs_diff x M)^2) S % 2^m := land_mod_eq_of_mod_eq (K^2) ((abs_diff x M)^2) S m h4
  have h6 : Nat.land ((abs_diff x M)^2) S < 2^m := by
    have h : Nat.land ((abs_diff x M)^2) S ≤ S := land_le_right ((abs_diff x M)^2) S
    omega
  exact mod_eq_of_lt x (Nat.land ((abs_diff x M)^2) S) m h5 hx_lt h6

lemma exists_k_from_x (M S x : ℕ) (hS : S = 2 * M + 1) (hx_le : x ≤ S)
  (hx : x = Nat.land ((abs_diff x M)^2) S) :
  ∃ k : ℕ, k + Nat.land (k^2) S = M := by
  by_cases h : x ≤ M
  · use M - x
    have h1 : abs_diff x M = M - x := by
      rw [abs_diff]
      exact if_pos h
    have h2 : x = Nat.land ((M - x)^2) S := by
      rw [h1] at hx
      exact hx
    have h3 : M - x + Nat.land ((M - x)^2) S = M := by omega
    exact h3
  · have h1 : abs_diff x M = x - M := by
      rw [abs_diff]
      exact if_neg h
    have h2 : x = Nat.land ((x - M)^2) S := by
      rw [h1] at hx
      exact hx
    let z := x - M - 1
    have h3 : z + 1 = x - M := by omega
    have h4 : x = Nat.land ((z + 1)^2) S := by
      rw [h3]
      exact h2
    have h5 : Nat.land (z^2) S = S - x := reverse_symmetry_z z M S x hS hx_le h3 h4
    use z
    have h6 : z + (S - x) = M := by omega
    omega
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (n : ℕ) : ∃ k : ℕ, Nat.xor (k ^ 2) ((k + 1) ^ 2) = (2 * n + 1) ^ 2 := by
  -- EVOLVE-BLOCK-START
  let S := (2 * n + 1) ^ 2
  let M := 2 * n * (n + 1)
  have hS : S = 2 * M + 1 := by ring
  have hM : M % 4 = 0 := by
    have h : M = 4 * (n * (n + 1) / 2) := by
      -- 2n(n+1) = 4 * (n(n+1)/2)
      linear_combination2←2*.div_mul_cancel n.even_mul_succ_self.two_dvd
    rw [h]
    exact Nat.mul_mod_right 4 _
  have h_exist : ∃ k : ℕ, k + Nat.land (k ^ 2) S = M := by
    have hm_lt : S < 2^S := by exact S.lt_two_pow_self
    let K := construct_k S M S
    have hK : (K + Nat.land (K^2) S) % 2^S = M % 2^S := construct_k_valid S M S hM
    have hx : Nat.land (K^2) S = Nat.land ((abs_diff (Nat.land (K^2) S) M)^2) S := exact_fixed_point_x M S S K hm_lt hK
    let x := Nat.land (K^2) S
    have hx_le : x ≤ S := land_le_right (K^2) S
    exact exists_k_from_x M S x hS hx_le hx
  obtain ⟨k, hk⟩ := h_exist
  use k
  exact k_eq_M_implies_xor_eq_S k M S hS hk
  -- EVOLVE-BLOCK-END
