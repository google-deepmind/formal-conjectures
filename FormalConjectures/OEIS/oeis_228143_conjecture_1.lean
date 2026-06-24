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




open BigOperators Matrix Nat

/--
A005259: The auxiliary sequence used for the Hankel matrix, defined as
$$\sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}^2$$
-/
def A005259' (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (n.choose k)^2 * ((Nat.choose (n + k) k))^2

/--
A228143: Determinant of the $(n+1) \times (n+1)$ Hankel-type matrix with $(i,j)$-entry equal to A005259$(i+j)$ for all $i,j = 0,\dots,n$.
The entry function A005259 is taken to be $\sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}^2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let dim : Type := Fin (n + 1)
  -- Matrix entries are lifted to ℤ for determinant calculation
  let M : Matrix dim dim ℤ :=
    Matrix.of fun i j => (A005259' (i.val + j.val) : ℤ)
  -- The sequence is known to be non-negative integers (nonn).
  M.det.natAbs

open PowerSeries

/-- The power series $A(x/3) = \sum_{n=0}^\infty \frac{a(n)}{3^n} x^n$ over ℚ. -/
noncomputable def OGF_A_scaled : PowerSeries ℚ :=
  PowerSeries.mk fun n => (a n : ℚ) / (3 ^ n : ℚ)

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

lemma alt_sum_choose (n : ℕ) :
  ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) * ((n + k).choose k : ℤ) = (-1 : ℤ) ^ n := by
  push_cast [Nat.add_choose_eq, false,mul_assoc, true,eq_comm, Finset.mul_sum]
  simp_all(config := {singlePass:=1})[mul_left_comm, Finset.Nat.antidiagonal_eq_map _,← Finset.mem_range_succ_iff,pow_add]
  trans∑p ∈.range (n + 1),∑ a ∈.range (n + 1),n.choose p *(n.choose a*((-1)^p*p.choose a))
  · rw [← Finset.sum_comm, Finset.sum_eq_single_of_mem n (by bound) fun and R M=>(( Finset.sum_range_add_sum_Ico _) (@List.mem_range.1 R).le).symm.trans (by_contra fun and' =>absurd ((add_pow (-1) (1) (n-and):).symm) ?_)]
    · exact(( Finset.sum_range_succ _ _).trans (by simp_all[Nat.choose_eq_zero_of_lt ∘ Finset.mem_range.1])).symm
    simp_all only[←mul_assoc, zero_pow (and.sub_ne_zero_of_lt (M.lt_of_le (Finset.mem_range_succ_iff.1 R))), Finset.sum_Ico_eq_sum_range, mul_comm, one_pow, mul_one,pow_add,Ne,neg_add_cancel, zero_add,Nat.choose_eq_zero_of_lt ∘ Finset.mem_range.1]
    exact and' ∘mod_cast (by(norm_num[ ← Finset.mul_sum _,n.succ_sub, and.add_sub_cancel_left, mul_assoc, mul_left_comm (@(n -and).choose @_ : ℤ),n.choose_mul, ←and.le_sub_iff_add_le', Finset.mem_range_succ_iff.1 R,.]))
  · exact Finset.sum_congr ↑rfl fun and x =>( Finset.sum_subset ↑(List.range_subset.mpr ↑(List.mem_range.1 ↑x ) ) fun and I I=>Nat.choose_eq_zero_of_lt (not_lt.mp (I.comp (List.mem_range.mpr)))▸by·ring).symm.trans ( Finset.sum_congr ↑rfl ↑(by simp_all [Nat]))











lemma choose_mul_choose_eq (n k : ℕ) : (n.choose k) * ((n + k).choose k) = ((n + k).choose (2 * k)) * ((2 * k).choose k) := by
  simp_all only[le_add_self,Nat.add_le_add_right, two_mul,Nat.choose_mul,Nat.add_sub_cancel, false,Nat.mul_comm]

lemma lucas_3 (n k : ℕ) : (n.choose k : ℤ) ≡ (n / 3).choose (k / 3) * (n % 3).choose (k % 3) [ZMOD 3] := by
  refine Eq.symm ↑(mod_cast n.strongRec @(? _) (k : ℕ))
  rintro(F | S | S | S) and(F | S | S|F)
  · rfl
  · rfl
  · rfl
  · norm_num[add_assoc]
  · rfl
  · rfl
  · rfl
  · simp_all![ add_assoc]
  · rfl
  · rfl
  · rfl
  · simp_all![add_assoc]
  · norm_num
  · norm_num
  · norm_num[← and S (by valid),Nat.add_mod, add_assoc,Nat.choose]
    omega
  · norm_num[Nat.choose, add_assoc, add_mul,← and S (by repeat constructor)]
    exact (by_contra fun and' =>absurd (and S · F) (absurd (F.add_div_right ·▸F.add_mod_right (3)▸ and S · _) ∘by valid))

lemma choose_2k_mod_3 (k : ℕ) : ((2 * k).choose k : ℤ) ≡ 0 [ZMOD 3] ∨ ((2 * k).choose k : ℤ) ≡ (-1 : ℤ)^k [ZMOD 3] := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    rcases eq_or_ne k 0 with rfl | hk0
    · right; rfl
    have h_mod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases h_mod with hm0 | hm1 | hm2
    · have h2 : (2 * k) % 3 = 0 := by push_cast[*, true,Nat.mul_mod]
      have h3 : (2 * k) / 3 = 2 * (k / 3) := by exact (3).mul_div_assoc (2) ((3).dvd_of_mod_eq_zero hm0)
      have h_lucas := lucas_3 (2 * k) k
      exact (ih (k/3) (by valid)).imp (h_lucas.trans ∘by norm_num[*]) (h_lucas.trans ∘by norm_num[*,Nat.mul_div_cancel' ((3).dvd_of_mod_eq_zero hm0)▸pow_mul _ _ _])
    · have h2 : (2 * k) % 3 = 2 := by rw [Nat.mul_mod,hm1]
      have h3 : (2 * k) / 3 = 2 * (k / 3) := by ((omega))
      have h_lucas := lucas_3 (2 * k) k
      simp_all -contextual [k.mod_add_div (3)▸pow_add _ _ _,pow_mul,Int.ModEq]
      exact (ih _ (by valid)).imp (·.mul_right _) ((Int.ModEq.mul_right _) ·|>.trans (Int.modEq_of_dvd (by valid)))
    · have h2 : (2 * k) % 3 = 1 := by rw [Nat.mul_mod _,hm2]
      have h3 : (2 * k) / 3 = 2 * (k / 3) + 1 := by omega
      have h_lucas := lucas_3 (2 * k) k
      exact (.inl (by apply h2▸hm2▸h_lucas))

lemma choose_n_plus_k_mod_3 (k n : ℕ) :
  ((2 * k).choose k : ℤ) ≡ 0 [ZMOD 3] ∨
  (((n + k).choose (2 * k) : ℤ) ≡ 0 [ZMOD 3] ∨ ((n + k).choose (2 * k) : ℤ) ≡ 1 [ZMOD 3]) := by
  induction k using Nat.strongRecOn generalizing n with
  | ind k ih =>
    rcases eq_or_ne k 0 with rfl | hk0
    · right; right
      norm_num
    have h_mod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    have hk_eq : k = 3 * (k / 3) + k % 3 := (Nat.div_add_mod k 3).symm
    rcases h_mod with hm0 | hm1 | hm2
    · have h2 : (2 * k) % 3 = 0 := by rw [Nat.mul_mod _,hm0]
      have h3 : (2 * k) / 3 = 2 * (k / 3) := by exact (3).mul_div_assoc (2) ((3).dvd_of_mod_eq_zero ↑(hm0))
      have h_lucas := lucas_3 (2 * k) k
      have h_lucas2 := lucas_3 (n + k) (2 * k)
      norm_num[hm0,h3,h2, (by valid:(n+k)/3=n/3+k/3)] at h_lucas‹_›⊢
      exact (ih _ (by valid) (_)).imp h_lucas.trans (.imp h_lucas2.trans (h_lucas2).trans)
    · have h2 : (2 * k) % 3 = 2 := by rw [Nat.mul_mod _,hm1]
      have h3 : (2 * k) / 3 = 2 * (k / 3) := by omega
      have h_lucas := lucas_3 (2 * k) k
      have h_lucas2 := lucas_3 (n + k) (2 * k)
      use if a:(n+k)%3=0 then(? _)else if I:(n+k)%3=1 then(? _)else(? _)
      · use .inr<|.inl (by apply h2▸a▸h_lucas2)
      · exact (.inr (.inl (by apply I▸h2▸h_lucas2)))
      norm_num[hm1,h2,h3, (by valid:(n+k)%3=2),n.add_div] at h_lucas h_lucas2
      exact (ih @_ (by valid) (_)).imp (h_lucas.trans.comp (·.mul_right (2))) (.imp (h_lucas2.trans ∘.trans (by rw [if_neg (by valid),add_zero])) (h_lucas2.trans ∘.trans (by rw [if_neg (by valid), add_zero])))
    · have h2 : (2 * k) % 3 = 1 := by push_cast[hm2,Nat.mul_mod]
      have h3 : (2 * k) / 3 = 2 * (k / 3) + 1 := by focus ·omega
      have h_lucas := lucas_3 (2 * k) k
      have h_lucas2 := lucas_3 (n + k) (2 * k)
      use .inl (by apply hm2▸h2▸h_lucas)

lemma choose_square_mod_3_step1_helper (A B : ℤ) (k : ℕ)
  (hA : A ≡ 0 [ZMOD 3] ∨ A ≡ 1 [ZMOD 3])
  (hB : B ≡ 0 [ZMOD 3] ∨ B ≡ (-1 : ℤ)^k [ZMOD 3]) :
  (A * B)^2 ≡ (-1 : ℤ)^k * (A * B) [ZMOD 3] := by
  simp_all only [Int.ModEq, one_mul,sq]
  cases hA with cases hB with norm_num[*,Int.mul_emod]

lemma choose_square_mod_3_step1 (n k : ℕ) :
  ((n + k).choose (2 * k) * (2 * k).choose k : ℤ)^2 ≡ (-1 : ℤ)^k * ((n + k).choose (2 * k) * (2 * k).choose k : ℤ) [ZMOD 3] := by
  have h1 := choose_2k_mod_3 k
  have h2 := choose_n_plus_k_mod_3 k n
  have h3 := choose_square_mod_3_step1_helper ((n + k).choose (2 * k)) ((2 * k).choose k) k
  exact (em _).elim ↑(h3 · h1) (by push_cast [sq, false,Int.ModEq, mul_zero, false,Int.mul_emod,show (@ _)% (3: Int)=0 from h2.resolve_right ·])

lemma choose_square_mod_3 (n k : ℕ) :
  ((n.choose k : ℤ) * ((n + k).choose k : ℤ))^2 ≡ (-1 : ℤ)^k * (n.choose k : ℤ) * ((n + k).choose k : ℤ) [ZMOD 3] := by
  have h1 : (n.choose k : ℤ) * ((n + k).choose k : ℤ) = ((n + k).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) := by
    exact_mod_cast choose_mul_choose_eq n k
  rw [h1]
  have h2 := choose_square_mod_3_step1 n k
  have h3 : (-1 : ℤ) ^ k * ↑(n.choose k) * ↑((n + k).choose k) = (-1 : ℤ) ^ k * (↑((n + k).choose (2 * k)) * ↑((2 * k).choose k)) := by
    rw [← h1]
    ring
  rw [h3]
  exact h2

lemma A005259_mod_3 (n : ℕ) : (A005259' n : ℤ) ≡ (-1 : ℤ) ^ n [ZMOD 3] := by
  have h1 := alt_sum_choose n
  have h2 : ∀ k, ((n.choose k : ℤ) * ((n + k).choose k : ℤ))^2 ≡ (-1 : ℤ)^k * (n.choose k : ℤ) * ((n + k).choose k : ℤ) [ZMOD 3] := fun k => choose_square_mod_3 n k
  delta degree A005259'
  zify [Int.ModEq.sum fun and x => h2 _, ← h1, ←mul_pow]

noncomputable def P_mat (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i j => if i = j then 1 else if j.val = 0 then -(-1 : ℤ) ^ i.val else 0

lemma det_P_mat (n : ℕ) : (P_mat n).det = 1 := by
  delta and P_mat
  norm_num[Matrix.det_succ_column_zero,Fin.sum_univ_succ,pow_succ]
  rw[Matrix.det_of_upperTriangular fun and=> by aesop, Finset.sum_eq_zero fun and y=>? _,neg_zero, add_zero]
  · push_cast[eq_self,Matrix.submatrix_apply, Finset.prod_const_one]
  · norm_num[Matrix.det_eq_zero_of_column_eq_zero and, Fin.succ_ne_zero]

lemma P_mat_mul_M_val (n : ℕ) (i j : Fin (n + 1)) (hi : i.val ≥ 1) :
  (P_mat n * Matrix.of (fun (u v : Fin (n + 1)) => (A005259' (u.val + v.val) : ℤ))) i j =
  (A005259' (i.val + j.val) : ℤ) - (-1 : ℤ) ^ i.val * (A005259' j.val : ℤ) := by
  norm_num [P_mat, sub_eq_add_neg, true,Matrix.mul_apply]at*
  norm_num[i.ext_iff,mt hi.trans_eq,Finset.sum_ite,Finset.filter_eq]
  norm_num[ Fin.val_injective.eq_iff, Finset.filter_eq]

lemma P_mat_mul_M_div_3 (n : ℕ) (i j : Fin (n + 1)) (hi : i.val ≥ 1) :
  3 ∣ (P_mat n * Matrix.of (fun (u v : Fin (n + 1)) => (A005259' (u.val + v.val) : ℤ))) i j := by
  have h_val := P_mat_mul_M_val n i j hi
  rw [h_val]
  have h1 := A005259_mod_3 (i.val + j.val)
  have h2 := A005259_mod_3 j.val
  apply(( h1.trans (by rw [pow_add])).trans (h2.mul_left _).symm)|>.symm.dvd

noncomputable def D_mat (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.diagonal (fun i => if i.val = 0 then 1 else 3)

lemma det_D_mat (n : ℕ) : (D_mat n).det = 3 ^ n := by
  delta D_mat
  norm_num[Finset.prod]

noncomputable def M_prime (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i j => if i.val = 0 then (A005259' j.val : ℤ) else
    ((P_mat n * Matrix.of fun (u v : Fin (n + 1)) => (A005259' (u.val + v.val) : ℤ)) i j) / 3

lemma P_mul_M_eq_D_mul_M_prime (n : ℕ) :
  P_mat n * Matrix.of (fun (u v : Fin (n + 1)) => (A005259' (u.val + v.val) : ℤ)) = D_mat n * M_prime n := by
  ext i j
  by_cases h : i.val = 0
  · simp_all[Matrix.mul_apply,P_mat,D_mat]
    simp_all[M_prime,Matrix.diagonal,comm]
  · rw [D_mat, Matrix.diagonal_mul]
    have hd : 3 ∣ (P_mat n * Matrix.of (fun (u v : Fin (n + 1)) => (A005259' (u.val + v.val) : ℤ))) i j := P_mat_mul_M_div_3 n i j (by omega)
    have h_prime : M_prime n i j = ((P_mat n * Matrix.of (fun (u v : Fin (n + 1)) => (A005259' (u.val + v.val) : ℤ))) i j) / 3 := by
      unfold M_prime
      simp [h]
    rw [h_prime]
    simp [h]
    exact (Int.mul_ediv_cancel' hd).symm

lemma a_div_3_pow (n : ℕ) : 3^n ∣ a n := by
  have hd := P_mul_M_eq_D_mul_M_prime n
  have Hdet : (P_mat n * Matrix.of (fun (u v : Fin (n + 1)) => (A005259' (u.val + v.val) : ℤ))).det = (D_mat n * M_prime n).det := by rw [hd]
  rw [Matrix.det_mul, det_P_mat n, one_mul, Matrix.det_mul, det_D_mat n] at Hdet
  have H3 : (3 ^ n : ℤ) ∣ (Matrix.of (fun (u v : Fin (n + 1)) => (A005259' (u.val + v.val) : ℤ))).det := by
    exact ⟨(M_prime n).det, Hdet⟩
  have hdvd : (3 ^ n : ℤ) ∣ (a n : ℤ) := by
    have h_a : (a n : ℤ) = ((Matrix.of (fun (u v : Fin (n + 1)) => (A005259' (u.val + v.val) : ℤ))).det.natAbs : ℤ) := rfl
    rw [h_a]
    exact Int.dvd_natAbs.mpr H3
  exact Int.ofNat_dvd.mp hdvd


lemma choose_square_mod_4 (n k : ℕ) (hk : k ≥ 1) :
  ((n.choose k : ℤ) * ((n + k).choose k : ℤ))^2 ≡ 0 [ZMOD 4] := by
  refine(pow_dvd_pow_of_dvd (mod_cast if a:_ then⟨0,a⟩else n.add_choose_eq _ _▸?_: (2 : Int) ∣ _) 2).modEq_zero_int
  simp_all[mul_left_comm, false,k.choose_symm (Finset.mem_range_succ_iff.1 _), Finset.Nat.antidiagonal_eq_map _, Finset.mul_sum]
  have:=k.sum_range_choose▸ Finset.mul_sum _ _ (n.choose k)
  replace a : ∀ a ∈ Finset.range (k + 1),n.choose k*(n.choose a*(k.choose a)) % 2 =n.choose k*k.choose a%2
  · simp_all[mul_left_comm (n.choose k),n.choose_mul,n.choose_eq_zero_iff,Nat.mod_two_of_bodd,Nat.lt_succ]
  · exact (2).dvd_of_mod_eq_zero (by rw [ Finset.sum_nat_mod, Finset.sum_congr ↑rfl a,← Finset.sum_nat_mod, this.symm, ((dvd_pow_self (2 : ℕ) (ne_zero_of_lt @hk)).mul_left @_).modEq_zero_nat])

lemma A005259_mod_4 (n : ℕ) : (A005259' n : ℤ) ≡ 1 [ZMOD 4] := by
  have h1 : ∀ k ≥ 1, ((n.choose k : ℤ) * ((n + k).choose k : ℤ))^2 ≡ 0 [ZMOD 4] := fun k => choose_square_mod_4 n k
  push_cast [Int.ModEq, mul_pow, A005259', ·≥·]at *
  exact (.trans (by rw [ Finset.sum_int_mod, Finset.sum_range_succ', Finset.sum_eq_zero fun and x => h1 _ and.succ_pos]) (by norm_num))

noncomputable def P_mat4 (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i j => if i = j then 1 else if j.val = 0 then -1 else 0

lemma det_P_mat4 (n : ℕ) : (P_mat4 n).det = 1 := by
  delta and P_mat4
  simp_all -contextual[Matrix.det_succ_column_zero]
  norm_num[Fin.sum_univ_succ,Fin.succ_ne_zero,pow_add]
  rewrite [ Finset.sum_eq_zero fun and x =>?_, add_zero]
  · exact (congr_arg _ (funext₂ (by norm_num[Matrix.one_apply,·.succ_ne_zero]))).trans Matrix.det_one
  norm_num[Fin.succ_ne_zero,Fin.succAbove,<-Matrix.exists_mulVec_eq_zero_iff,funext_iff,Matrix.submatrix]
  norm_num[Matrix.mulVec,dotProduct,ite_eq_iff]at*
  use fun p=>ite (p =and) (1) 0, ⟨and,by simp_all⟩, fun and=> Finset.sum_eq_zero fun and y=>ite_eq_right_iff.2 fun and=>if_neg (by cases· with grind)

lemma P_mat4_mul_M_val (n : ℕ) (i j : Fin (n + 1)) (hi : i.val ≥ 1) :
  (P_mat4 n * Matrix.of (fun (u v : Fin (n + 1)) => (A005259' (u.val + v.val) : ℤ))) i j =
  (A005259' (i.val + j.val) : ℤ) - (A005259' j.val : ℤ) := by
  simp_all -contextual [P_mat4,Matrix.mul_apply,Nat.one_le_iff_ne_zero, sub_eq_add_neg]
  simp_all[Finset.sum_ite,Finset.filter_eq]

lemma P_mat4_mul_M_div_4 (n : ℕ) (i j : Fin (n + 1)) (hi : i.val ≥ 1) :
  4 ∣ (P_mat4 n * Matrix.of (fun (u v : Fin (n + 1)) => (A005259' (u.val + v.val) : ℤ))) i j := by
  have h_val := P_mat4_mul_M_val n i j hi
  rw [h_val]
  have h1 := A005259_mod_4 (i.val + j.val)
  have h2 := A005259_mod_4 j.val
  exact (h1.trans h2.symm).symm.dvd

noncomputable def D_mat4 (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.diagonal (fun i => if i.val = 0 then 1 else 4)

lemma det_D_mat4 (n : ℕ) : (D_mat4 n).det = 4 ^ n := by
  delta D_mat4
  norm_num[(n).succ_sub_one, false, Finset.prod]

noncomputable def M_prime4 (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i j => if i.val = 0 then (A005259' j.val : ℤ) else
    ((P_mat4 n * Matrix.of fun (u v : Fin (n + 1)) => (A005259' (u.val + v.val) : ℤ)) i j) / 4

lemma P_mul_M_eq_D_mul_M_prime4 (n : ℕ) :
  P_mat4 n * Matrix.of (fun (u v : Fin (n + 1)) => (A005259' (u.val + v.val) : ℤ)) = D_mat4 n * M_prime4 n := by
  ext i j
  by_cases h : i.val = 0
  · norm_num[Matrix.mul_apply,P_mat4,D_mat4,M_prime4,h]
    simp_all[comm, Finset.sum_ite]
  · rw [D_mat4, Matrix.diagonal_mul]
    have hd : 4 ∣ (P_mat4 n * Matrix.of (fun (u v : Fin (n + 1)) => (A005259' (u.val + v.val) : ℤ))) i j := P_mat4_mul_M_div_4 n i j (by omega)
    have h_prime : M_prime4 n i j = ((P_mat4 n * Matrix.of (fun (u v : Fin (n + 1)) => (A005259' (u.val + v.val) : ℤ))) i j) / 4 := by
      unfold M_prime4
      simp [h]
    rw [h_prime]
    simp [h]
    exact (Int.mul_ediv_cancel' hd).symm

lemma a_div_4_pow (n : ℕ) : 4^n ∣ a n := by
  have hd := P_mul_M_eq_D_mul_M_prime4 n
  have Hdet : (P_mat4 n * Matrix.of (fun (u v : Fin (n + 1)) => (A005259' (u.val + v.val) : ℤ))).det = (D_mat4 n * M_prime4 n).det := by rw [hd]
  rw [Matrix.det_mul, det_P_mat4 n, one_mul, Matrix.det_mul, det_D_mat4 n] at Hdet
  have H4 : (4 ^ n : ℤ) ∣ (Matrix.of (fun (u v : Fin (n + 1)) => (A005259' (u.val + v.val) : ℤ))).det := by
    exact ⟨(M_prime4 n).det, Hdet⟩
  have hdvd : (4 ^ n : ℤ) ∣ (a n : ℤ) := by
    have h_a : (a n : ℤ) = ((Matrix.of (fun (u v : Fin (n + 1)) => (A005259' (u.val + v.val) : ℤ))).det.natAbs : ℤ) := rfl
    rw [h_a]
    exact Int.dvd_natAbs.mpr H4
  exact Int.ofNat_dvd.mp hdvd

def A005259_comp (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (n.choose k)^2 * ((Nat.choose (n + k) k))^2

def a_comp (n : ℕ) : ℕ :=
  let dim : Type := Fin (n + 1)
  let M : Matrix dim dim ℤ :=
    Matrix.of fun i j => (A005259_comp (i.val + j.val) : ℤ)
  M.det.natAbs

lemma a_comp_val_1 : a_comp 1 = 48 := by decide

lemma a_val_1 : a 1 = 48 := by
  have h : a = a_comp := by
    unfold a a_comp A005259' A005259_comp
    rfl
  rw [h]
  exact a_comp_val_1

lemma a_mod_16 (n : ℕ) (hn : n ≥ 1) : 16 ∣ a n := by
  have h4 := a_div_4_pow n
  cases n with
  | zero => omega
  | succ m =>
    cases m with
    | zero =>
      rw [a_val_1]
      exact ⟨3, rfl⟩
    | succ m' =>
      have h_pow : 16 ∣ 4 ^ (m' + 2) := by
        use 4 ^ m'
        ring
      exact dvd_trans h_pow h4

lemma a_div_16_mul_3_pow (n : ℕ) (hn : n ≥ 1) : 16 * 3^n ∣ a n := by
  have h16 := a_mod_16 n hn
  have h3 := a_div_3_pow n
  have h_coprime : IsCoprime (16 : ℤ) (3^n : ℤ) := by
    have hc : IsCoprime (16 : ℤ) (3 : ℤ) := by norm_num
    exact IsCoprime.pow_right hc
  rcases h_coprime with ⟨x, y, hxy⟩
  have h_int16 : (16 : ℤ) ∣ (a n : ℤ) := Int.ofNat_dvd.mpr h16
  have h_int3 : (3^n : ℤ) ∣ (a n : ℤ) := Int.ofNat_dvd.mpr h3
  rcases h_int16 with ⟨k1, hk1⟩
  rcases h_int3 with ⟨k2, hk2⟩
  have h4 : ((16 * 3 ^ n : ℕ) : ℤ) ∣ (a n : ℤ) := by
    have hc : ((16 * 3 ^ n : ℕ) : ℤ) = 16 * (3 ^ n : ℤ) := by push_cast; rfl
    rw [hc]
    use (x * k2 + y * k1)
    calc (a n : ℤ) = (a n : ℤ) * 1 := by ring
    _ = (a n : ℤ) * (x * 16 + y * 3 ^ n) := by rw [hxy]
    _ = 16 * x * (a n : ℤ) + 3 ^ n * y * (a n : ℤ) := by ring
    _ = 16 * x * (3 ^ n * k2) + 3 ^ n * y * (16 * k1) := by
      congr 1
      · rw [hk2]
      · rw [hk1]
    _ = 16 * 3 ^ n * (x * k2 + y * k1) := by ring
  exact Int.ofNat_dvd.mp h4

noncomputable def B_seq (n : ℕ) : ℤ :=
  (a n : ℤ) / (3 ^ n : ℤ)

lemma B_seq_zero : B_seq 0 = 1 := by
  constructor

lemma B_seq_mod_16 (n : ℕ) (hn : n ≥ 1) : 16 ∣ B_seq n := by
  have h := a_div_16_mul_3_pow n hn
  have h_int : (16 * 3^n : ℤ) ∣ (a n : ℤ) := Int.ofNat_dvd.mpr h
  unfold B_seq
  rcases h_int with ⟨k, hk⟩
  have hz : (3 ^ n : ℤ) ≠ 0 := by positivity
  have hk_rw : (a n : ℤ) = (16 * k) * 3^n := by
    calc (a n : ℤ) = 16 * 3^n * k := hk
    _ = (16 * k) * 3^n := by ring
  rw [hk_rw, Int.mul_ediv_cancel (16 * k) hz]
  use k

noncomputable def B_series : PowerSeries ℤ :=
  PowerSeries.mk B_seq

lemma map_B_series :
  PowerSeries.map (Int.castRingHom ℚ) B_series = OGF_A_scaled := by
  ext n
  simp only [PowerSeries.coeff_map, B_series, PowerSeries.coeff_mk, B_seq, OGF_A_scaled, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Int.castRingHom]
  have h_div : (3 ^ n : ℤ) ∣ (a n : ℤ) := by
    have h := a_div_3_pow n
    exact Int.ofNat_dvd.mpr h
  have h_nz : (3 ^ n : ℤ) ≠ 0 := by positivity
  rw [Int.cast_div h_div (by exact Int.cast_ne_zero.mpr h_nz)]
  push_cast
  rfl

noncomputable def Y_seq (n : ℕ) : ℤ :=
  if n = 0 then 0 else B_seq n / 16

noncomputable def Y_series : PowerSeries ℤ :=
  PowerSeries.mk Y_seq

lemma B_series_eq_1_plus_16_Y : B_series = 1 + 16 * Y_series := by
  ext n
  cases n with
  | zero => aesop
  | succ n =>
    have h_B : PowerSeries.coeff (n + 1) B_series = B_seq (n + 1) := by
      unfold B_series
      rw [PowerSeries.coeff_mk]
    have h_Y : PowerSeries.coeff (n + 1) Y_series = Y_seq (n + 1) := by
      unfold Y_series
      rw [PowerSeries.coeff_mk]
    have h_add : PowerSeries.coeff (n + 1) (1 + 16 * Y_series : PowerSeries ℤ) = PowerSeries.coeff (n + 1) 1 + PowerSeries.coeff (n + 1) (16 * Y_series) := by
      exact map_add (PowerSeries.coeff (n + 1)) 1 (16 * Y_series)
    have h_one : PowerSeries.coeff (n + 1) (1 : PowerSeries ℤ) = 0 := by
      rw [PowerSeries.coeff_one]
      exact if_neg (Nat.succ_ne_zero n)
    have h_mul : PowerSeries.coeff (n + 1) (16 * Y_series : PowerSeries ℤ) = 16 * PowerSeries.coeff (n + 1) Y_series := by
      apply PowerSeries.coeff_C_mul
    rw [h_B, h_add, h_one, zero_add, h_mul, h_Y]
    unfold Y_seq
    have h_nz : n + 1 ≠ 0 := Nat.succ_ne_zero n
    simp only [h_nz, ↓reduceIte]
    have h_mod := B_seq_mod_16 (n + 1) (Nat.succ_pos n)
    exact (Int.mul_ediv_cancel' h_mod).symm

lemma Y_series_zero : PowerSeries.coeff 0 Y_series = 0 := by
  unfold Y_series
  rw [PowerSeries.coeff_mk]
  simp [Y_seq]







def ValuationGe (m : ℕ) (S : PowerSeries ℤ) : Prop :=
  ∀ k < m, PowerSeries.coeff k S = 0

lemma ValuationGe_zero (S : PowerSeries ℤ) : ValuationGe 0 S := by
  intro k hk
  omega

lemma ValuationGe_mul {m1 m2 : ℕ} {S1 S2 : PowerSeries ℤ} (h1 : ValuationGe m1 S1) (h2 : ValuationGe m2 S2) :
  ValuationGe (m1 + m2) (S1 * S2) := by
  intro k hk
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  have h_cases : i < m1 ∨ j < m2 := by omega
  rcases h_cases with hi | hj
  · have hA := h1 i hi
    rw [hA, zero_mul]
  · have hB := h2 j hj
    rw [hB, mul_zero]

lemma ValuationGe_add {m : ℕ} {S1 S2 : PowerSeries ℤ} (h1 : ValuationGe m S1) (h2 : ValuationGe m S2) :
  ValuationGe m (S1 + S2) := by
  intro k hk
  rw [map_add, h1 k hk, h2 k hk, add_zero]

lemma ValuationGe_pow_ge_one {m : ℕ} (hm : m ≥ 1) {B : PowerSeries ℤ} (hB : ValuationGe 1 B) : ValuationGe 1 (B^m) := by
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  rw [hk, pow_succ]
  have h0 : ValuationGe 0 (B^k) := ValuationGe_zero (B^k)
  have h_mul := ValuationGe_mul h0 hB
  rw [zero_add] at h_mul
  exact h_mul

lemma diff_pow_eq (k : ℕ) (A B : PowerSeries ℤ) : ∃ Q : PowerSeries ℤ, A^(k+2) - B^(k+2) = (A - B) * Q ∧ (ValuationGe 1 A → ValuationGe 1 B → ValuationGe 1 Q) := by
  induction k with
  | zero =>
    use (A + B)
    constructor
    · ring
    · intro hA hB
      exact ValuationGe_add hA hB
  | succ k ih =>
    rcases ih with ⟨Q, hQ_eq, hQ_val⟩
    use A * Q + B^(k+2)
    constructor
    · calc A^(k+3) - B^(k+3) = A * (A^(k+2) - B^(k+2)) + (A - B) * B^(k+2) := by ring
        _ = A * ((A - B) * Q) + (A - B) * B^(k+2) := by rw [hQ_eq]
        _ = (A - B) * (A * Q + B^(k+2)) := by ring
    · intro hA hB
      have hQ1 := hQ_val hA hB
      have hAQ : ValuationGe 1 (A * Q) := by
        have hz := ValuationGe_zero Q
        have hmul := ValuationGe_mul hA hz
        rw [add_zero] at hmul
        exact hmul
      have hk2 : k + 2 ≥ 1 := by omega
      have hBm := ValuationGe_pow_ge_one hk2 hB
      exact ValuationGe_add hAQ hBm

lemma ValuationGe_diff_pow (n : ℕ) (k : ℕ) {A B : PowerSeries ℤ} (hdiff : ValuationGe (n + 1) (A - B)) (hA : ValuationGe 1 A) (hB : ValuationGe 1 B) :
  ValuationGe (n + 2) (A^(k+2) - B^(k+2)) := by
  rcases diff_pow_eq k A B with ⟨Q, hQ_eq, hQ_val⟩
  rw [hQ_eq]
  have hQ1 := hQ_val hA hB
  have hmul := ValuationGe_mul hdiff hQ1
  have h_add : n + 1 + 1 = n + 2 := by omega
  rw [h_add] at hmul
  exact hmul

lemma ValuationGe_const_mul {m : ℕ} (c : PowerSeries ℤ) {S : PowerSeries ℤ} (h : ValuationGe m S) : ValuationGe m (c * S) := by
  have h0 := ValuationGe_zero c
  have hmul := ValuationGe_mul h0 h
  rw [zero_add] at hmul
  exact hmul

lemma coeff_const_mul_pow_eq (n : ℕ) (k : ℕ) (c : PowerSeries ℤ) {A B : PowerSeries ℤ} (hdiff : ValuationGe (n + 1) (A - B)) (hA : ValuationGe 1 A) (hB : ValuationGe 1 B) :
  PowerSeries.coeff (n + 1) (c * A^(k+2)) = PowerSeries.coeff (n + 1) (c * B^(k+2)) := by
  have hge := ValuationGe_diff_pow n k hdiff hA hB
  have h_cmul := ValuationGe_const_mul c hge
  have h_sub : c * A^(k+2) - c * B^(k+2) = c * (A^(k+2) - B^(k+2)) := by ring
  rw [← h_sub] at h_cmul
  have hk_lt : n + 1 < n + 2 := by omega
  have hzero := h_cmul (n + 1) hk_lt
  have hsub2 : PowerSeries.coeff (n + 1) (c * A^(k+2) - c * B^(k+2)) = PowerSeries.coeff (n + 1) (c * A^(k+2)) - PowerSeries.coeff (n + 1) (c * B^(k+2)) := map_sub (PowerSeries.coeff (n + 1)) _ _
  rw [hsub2] at hzero
  exact sub_eq_zero.mp hzero

noncomputable def P_poly (X : PowerSeries ℤ) : PowerSeries ℤ :=
  (7 : PowerSeries ℤ) * X^2 + (28 : PowerSeries ℤ) * X^3 + (70 : PowerSeries ℤ) * X^4 + (112 : PowerSeries ℤ) * X^5 + (112 : PowerSeries ℤ) * X^6 + (64 : PowerSeries ℤ) * X^7 + (16 : PowerSeries ℤ) * X^8

lemma coeff_P_poly_eq (n : ℕ) {A B : PowerSeries ℤ} (hdiff : ValuationGe (n + 1) (A - B)) (hA : ValuationGe 1 A) (hB : ValuationGe 1 B) :
  PowerSeries.coeff (n + 1) (P_poly A) = PowerSeries.coeff (n + 1) (P_poly B) := by
  unfold P_poly
  simp only [map_add]
  have h2 := coeff_const_mul_pow_eq n 0 7 hdiff hA hB
  have h3 := coeff_const_mul_pow_eq n 1 28 hdiff hA hB
  have h4 := coeff_const_mul_pow_eq n 2 70 hdiff hA hB
  have h5 := coeff_const_mul_pow_eq n 3 112 hdiff hA hB
  have h6 := coeff_const_mul_pow_eq n 4 112 hdiff hA hB
  have h7 := coeff_const_mul_pow_eq n 5 64 hdiff hA hB
  have h8 := coeff_const_mul_pow_eq n 6 16 hdiff hA hB
  rw [h2, h3, h4, h5, h6, h7, h8]

lemma one_plus_two_X_pow_8 (X : PowerSeries ℤ) :
  (1 + (2 : PowerSeries ℤ) * X) ^ 8 = 1 + (16 : PowerSeries ℤ) * (X + P_poly X) := by
  unfold P_poly
  ring

noncomputable def X_seq (Y : ℕ → ℤ) : ℕ → ℤ
| 0 => 0
| n + 1 =>
  let prev_X : PowerSeries ℤ := PowerSeries.mk (fun k => if k < n + 1 then X_seq Y k else 0)
  Y (n + 1) - PowerSeries.coeff (n + 1) (P_poly prev_X)
termination_by n => n

noncomputable def X_series (Y : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk (X_seq (fun k => PowerSeries.coeff k Y))

lemma X_series_coeff_zero (Y : PowerSeries ℤ) : PowerSeries.coeff 0 (X_series Y) = 0 := by
  unfold X_series
  rw [PowerSeries.coeff_mk]
  simp_all[ X_seq]

noncomputable def trunc_ps (n : ℕ) (S : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk (fun k => if k < n then PowerSeries.coeff k S else 0)

lemma trunc_ps_coeff_lt (n : ℕ) (S : PowerSeries ℤ) (k : ℕ) (hk : k < n) :
  PowerSeries.coeff k (trunc_ps n S) = PowerSeries.coeff k S := by
  unfold trunc_ps
  rw [PowerSeries.coeff_mk, if_pos hk]

lemma trunc_ps_coeff_ge (n : ℕ) (S : PowerSeries ℤ) (k : ℕ) (hk : ¬(k < n)) :
  PowerSeries.coeff k (trunc_ps n S) = 0 := by
  unfold trunc_ps
  rw [PowerSeries.coeff_mk, if_neg hk]

lemma X_series_val_one (Y : PowerSeries ℤ) : ValuationGe 1 (X_series Y) := by
  intro k hk
  have hz : k = 0 := by omega
  rw [hz, X_series_coeff_zero]

lemma trunc_ps_val_one (n : ℕ) (S : PowerSeries ℤ) (hS : ValuationGe 1 S) : ValuationGe 1 (trunc_ps n S) := by
  intro k hk
  have hz : k = 0 := by omega
  rw [hz]
  by_cases h : 0 < n
  · rw [trunc_ps_coeff_lt n S 0 h]
    exact hS 0 (by omega)
  · rw [trunc_ps_coeff_ge n S 0 h]

lemma val_diff_trunc (n : ℕ) (S : PowerSeries ℤ) : ValuationGe n (S - trunc_ps n S) := by
  intro k hk
  have hsub : PowerSeries.coeff k (S - trunc_ps n S) = PowerSeries.coeff k S - PowerSeries.coeff k (trunc_ps n S) := map_sub _ _ _
  rw [hsub, trunc_ps_coeff_lt n S k hk, sub_self]

lemma X_series_coeff_succ (Y : PowerSeries ℤ) (n : ℕ) :
  PowerSeries.coeff (n + 1) (X_series Y) = PowerSeries.coeff (n + 1) Y - PowerSeries.coeff (n + 1) (P_poly (trunc_ps (n + 1) (X_series Y))) := by
  delta trunc_ps pow_one X_series
  norm_num[P_poly,X_seq]

lemma X_plus_P_poly_eq_Y_coeff (Y : PowerSeries ℤ) (n : ℕ) :
  PowerSeries.coeff (n + 1) (X_series Y + P_poly (X_series Y)) = PowerSeries.coeff (n + 1) Y := by
  have h1 := X_series_coeff_succ Y n
  have h2 : PowerSeries.coeff (n + 1) (X_series Y + P_poly (X_series Y)) = PowerSeries.coeff (n + 1) (X_series Y) + PowerSeries.coeff (n + 1) (P_poly (X_series Y)) := map_add _ _ _
  rw [h2, h1]
  have h_diff := val_diff_trunc (n + 1) (X_series Y)
  have hX1 := X_series_val_one Y
  have hT1 := trunc_ps_val_one (n + 1) (X_series Y) hX1
  have h_P := coeff_P_poly_eq n h_diff hX1 hT1
  rw [h_P]
  ring

lemma coeff_zero_P_poly (X : PowerSeries ℤ) (hX : PowerSeries.coeff 0 X = 0) :
  PowerSeries.coeff 0 (P_poly X) = 0 := by
  simp_all [P_poly, false_iff]

lemma X_plus_P_poly_eq_Y_zero (Y : PowerSeries ℤ) (hY0 : PowerSeries.coeff 0 Y = 0) :
  PowerSeries.coeff 0 (X_series Y + P_poly (X_series Y)) = PowerSeries.coeff 0 Y := by
  rw [map_add, X_series_coeff_zero]
  have h_P0 := coeff_zero_P_poly (X_series Y) (X_series_coeff_zero Y)
  rw [h_P0, zero_add, hY0]

lemma X_plus_P_poly_eq_Y (Y : PowerSeries ℤ) (hY0 : PowerSeries.coeff 0 Y = 0) :
  X_series Y + P_poly (X_series Y) = Y := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => exact X_plus_P_poly_eq_Y_zero Y hY0
  | succ n => exact X_plus_P_poly_eq_Y_coeff Y n

lemma X_series_pow_8 (Y : PowerSeries ℤ) (hY0 : PowerSeries.coeff 0 Y = 0) :
  (1 + 2 * X_series Y) ^ 8 = 1 + 16 * Y := by
  have h1 := one_plus_two_X_pow_8 (X_series Y)
  have h2 := X_plus_P_poly_eq_Y Y hY0
  rw [h2] at h1
  exact h1

lemma exists_seq_P (Y : PowerSeries ℤ) (hY0 : PowerSeries.coeff 0 Y = 0) :
  ∃ X : PowerSeries ℤ, PowerSeries.coeff 0 X = 0 ∧
    (1 + 2 * X) ^ 8 = 1 + 16 * Y := by
  use X_series Y
  exact ⟨X_series_coeff_zero Y, X_series_pow_8 Y hY0⟩



lemma exists_eighth_root_B :
  ∃ C : PowerSeries ℤ, C ^ 8 = B_series := by
  have hY0 := Y_series_zero
  have h_ex := exists_seq_P Y_series hY0
  rcases h_ex with ⟨X, _, hX⟩
  use (1 + 2 * X)
  rw [hX]
  exact B_series_eq_1_plus_16_Y.symm

-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : ∃ C : PowerSeries ℤ, (PowerSeries.map (Int.castRingHom ℚ)) (C ^ 8) = OGF_A_scaled := by
  -- EVOLVE-BLOCK-START
  obtain ⟨C, hC⟩ := exists_eighth_root_B
  use C
  rw [hC]
  exact map_B_series
  -- EVOLVE-BLOCK-END
