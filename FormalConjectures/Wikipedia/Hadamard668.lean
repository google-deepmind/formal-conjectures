/-
Copyright 2026 The Formal Conjectures Authors.

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

import FormalConjecturesUtil

/-!
# A Hadamard matrix of order 668

This file formalizes the order-668 construction announced by Levent Alpöge, Philippe Voinov,
Saul Reynolds-Haertle, and Claude.

## Structure of the construction

The announced data contain four sign sequences of length 166. Their positive supports have sizes
84, 83, 83, and 83, and form a type $H_4^*$ supplementary difference family: the sum of their
periodic autocorrelations is 664 at shift zero and $-4$ at every nonzero shift. The
Wallis--Whiteman bordered Goethals--Seidel construction turns precisely this data into a Hadamard
matrix of order $4(166+1)=668$.

## Verification strategy

The proof deliberately does not ask Lean to reduce all $668^2$ inner products. Instead it:

1. proves the Goethals--Seidel block identity symbolically for arbitrary circulant matrices;
2. proves autocorrelation symmetry, then checks the 83 representative nonzero shifts of the four
   seeds in 21 independent batches of at most four shifts (and checks the four row sums separately);
3. proves the three small border identities on $4\times4$ matrices; and
4. assembles the bordered block Gram matrix and transports it along
   `Fin 4 ⊕ (Fin 4 × Fin 166) ≃ Fin 668`.

Thus the only construction-specific computation is linear in the seed length. All certificates are
checked by Lean's kernel using `decide +kernel`; no native evaluator or trusted external result is
used.

*References:*
- [Order-668 construction](https://x.com/__alpoge__/status/2087504785952182273)
  by *Levent Alpöge et al.* (2026)
- [Construction credits](https://x.com/__alpoge__/status/2087504790435840207)
- [Supplementary difference sets with symmetry for Hadamard matrices](https://arxiv.org/abs/1809.05253)
  by *Dragomir Ž. Đoković* (2018)
-/

open Matrix

namespace Hadamard

private abbrev C := Fin 166
private abbrev Q := Fin 4

/-- The four binary seeds; set bits encode $+1$ and unset bits encode $-1$. -/
private def seedBits : Q → BitVec 166 :=
  ![0x125953fe2c4fbd9e46d5424b2a5fc58e084c372557#166,
    0x383e32a915b5fb694a447f07c65522b4c092deb770#166,
    0x71876112ff7760ef2e578e30ec225fd913e21a350#166,
    0x14c464e997f8fcd16f35c2988c8d32fce065d21947#166]

private def seed (q : Q) (i : C) : ℤ := if (seedBits q).getLsb i then 1 else -1

@[category test, AMS 15]
private lemma seed_sum (q : Q) : ∑ i, seed q i = if q = 0 then 2 else 0 := by
  fin_cases q <;> decide +kernel

private def rev : Matrix C C ℤ := (Equiv.neg C).permMatrix ℤ

private def circ (x : C → ℤ) : Matrix C C ℤ := Matrix.circulant x

@[category API, AMS 15]
private lemma rev_transpose : rev.transpose = rev := by
  change ((Equiv.neg C).permMatrix ℤ).transpose = (Equiv.neg C).permMatrix ℤ
  rw [Matrix.transpose_permMatrix]
  congr

@[category API, AMS 15]
private lemma rev_mul_rev : rev * rev = 1 := by
  have h : (Equiv.neg C : Equiv.Perm C) * Equiv.neg C = 1 := by
    ext i
    simp
  change (Equiv.neg C).permMatrix ℤ * (Equiv.neg C).permMatrix ℤ = 1
  rw [← Matrix.permMatrix_mul (R := ℤ) (Equiv.neg C) (Equiv.neg C)]
  rw [h, Matrix.permMatrix_one]

@[category API, AMS 15]
private lemma rev_mul_circ (x : C → ℤ) : rev * circ x = (circ x).transpose * rev := by
  rw [rev, circ, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [Matrix.circulant, sub_eq_add_neg, add_comm]

@[category API, AMS 15]
private lemma rev_mul_circ_transpose (x : C → ℤ) :
    rev * (circ x).transpose = circ x * rev := by
  rw [rev, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [circ, Matrix.circulant, sub_eq_add_neg, add_comm]

@[category API, AMS 15]
private lemma circ_comm (x y : C → ℤ) : circ x * circ y = circ y * circ x := by
  exact Matrix.Fin.circulant_mul_comm x y

@[category API, AMS 15]
private lemma circ_transpose_comm (x y : C → ℤ) :
    (circ x).transpose * circ y = circ y * (circ x).transpose := by
  simpa only [circ, Matrix.transpose_circulant] using
    Matrix.Fin.circulant_mul_comm (fun i => x (-i)) y

@[category API, AMS 15]
private lemma circ_transpose_comm_transpose (x y : C → ℤ) :
    (circ x).transpose * (circ y).transpose = (circ y).transpose * (circ x).transpose := by
  simpa only [circ, Matrix.transpose_circulant] using
    Matrix.Fin.circulant_mul_comm (fun i => x (-i)) (fun i => y (-i))

@[category API, AMS 15]
private lemma circ_normal (x : C → ℤ) :
    circ x * (circ x).transpose = (circ x).transpose * circ x := by
  exact (circ_transpose_comm x x).symm

@[category API, AMS 15]
private lemma circ_rev_mul_circ_rev (x y : C → ℤ) :
    (circ x * rev) * (circ y * rev) = circ x * (circ y).transpose := by
  calc
    (circ x * rev) * (circ y * rev) = circ x * (rev * circ y) * rev := by
      noncomm_ring
    _ = circ x * ((circ y).transpose * rev) * rev := by rw [rev_mul_circ]
    _ = circ x * (circ y).transpose * (rev * rev) := by noncomm_ring
    _ = circ x * (circ y).transpose := by rw [rev_mul_rev, Matrix.mul_one]

@[category API, AMS 15]
private lemma circ_rev_mul_circ_transpose_rev (x y : C → ℤ) :
    (circ x * rev) * ((circ y).transpose * rev) = circ x * circ y := by
  calc
    (circ x * rev) * ((circ y).transpose * rev) =
        circ x * (rev * (circ y).transpose) * rev := by noncomm_ring
    _ = circ x * (circ y * rev) * rev := by rw [rev_mul_circ_transpose]
    _ = circ x * circ y * (rev * rev) := by noncomm_ring
    _ = circ x * circ y := by rw [rev_mul_rev, Matrix.mul_one]

@[category API, AMS 15]
private lemma circ_transpose_rev_mul_circ_rev (x y : C → ℤ) :
    ((circ x).transpose * rev) * (circ y * rev) =
      (circ x).transpose * (circ y).transpose := by
  calc
    ((circ x).transpose * rev) * (circ y * rev) =
        (circ x).transpose * (rev * circ y) * rev := by noncomm_ring
    _ = (circ x).transpose * ((circ y).transpose * rev) * rev := by
      rw [rev_mul_circ]
    _ = (circ x).transpose * (circ y).transpose * (rev * rev) := by noncomm_ring
    _ = (circ x).transpose * (circ y).transpose := by rw [rev_mul_rev, Matrix.mul_one]

@[category API, AMS 15]
private lemma circ_transpose_rev_mul_circ_transpose_rev (x y : C → ℤ) :
    ((circ x).transpose * rev) * ((circ y).transpose * rev) =
      (circ x).transpose * circ y := by
  calc
    ((circ x).transpose * rev) * ((circ y).transpose * rev) =
        (circ x).transpose * (rev * (circ y).transpose) * rev := by noncomm_ring
    _ = (circ x).transpose * (circ y * rev) * rev := by rw [rev_mul_circ_transpose]
    _ = (circ x).transpose * circ y * (rev * rev) := by noncomm_ring
    _ = (circ x).transpose * circ y := by rw [rev_mul_rev, Matrix.mul_one]

@[category API, AMS 15]
private lemma circ_transpose_mul_circ_rev (x y : C → ℤ) :
    (circ x).transpose * (circ y * rev) = (circ y * rev) * circ x := by
  rw [Matrix.mul_assoc, rev_mul_circ]
  rw [← Matrix.mul_assoc, circ_transpose_comm]
  noncomm_ring

@[category API, AMS 15]
private lemma circ_transpose_mul_circ_transpose_rev (x y : C → ℤ) :
    (circ x).transpose * ((circ y).transpose * rev) =
      ((circ y).transpose * rev) * circ x := by
  rw [Matrix.mul_assoc, rev_mul_circ]
  rw [← Matrix.mul_assoc, circ_transpose_comm_transpose]
  noncomm_ring

private def gsBlocks (a b c d : C → ℤ) : Matrix Q Q (Matrix C C ℤ) :=
  let A := circ a
  let B := circ b
  let C := circ c
  let D := circ d
  !![A, B * rev, C * rev, D * rev;
     -(B * rev), A, D.transpose * rev, -(C.transpose * rev);
     -(C * rev), -(D.transpose * rev), A, B.transpose * rev;
     -(D * rev), C.transpose * rev, -(B.transpose * rev), A]

private def gsBlocksT (a b c d : C → ℤ) : Matrix Q Q (Matrix C C ℤ) :=
  let A := circ a
  let B := circ b
  let C := circ c
  let D := circ d
  !![A.transpose, -(B * rev), -(C * rev), -(D * rev);
     B * rev, A.transpose, -(D.transpose * rev), C.transpose * rev;
     C * rev, D.transpose * rev, A.transpose, -(B.transpose * rev);
     D * rev, -(C.transpose * rev), B.transpose * rev, A.transpose]

@[category API, AMS 15]
private lemma gsBlocks_transpose (a b c d : C → ℤ) (p q : Q) :
    (gsBlocks a b c d p q).transpose = gsBlocksT a b c d q p := by
  fin_cases p <;> fin_cases q <;>
    simp [gsBlocks, gsBlocksT, rev_transpose, rev_mul_circ, rev_mul_circ_transpose]

private def blockGram (a b c d : C → ℤ) (q r : Q) : Matrix C C ℤ :=
  ∑ p : Q, (gsBlocks a b c d p q).transpose * gsBlocks a b c d p r

private def autoSum (a b c d : C → ℤ) : Matrix C C ℤ :=
  (circ a).transpose * circ a + (circ b).transpose * circ b +
    (circ c).transpose * circ c + (circ d).transpose * circ d

@[category API, AMS 15]
private lemma blockGram_all (a b c d : C → ℤ) (q r : Q) :
    blockGram a b c d q r = if q = r then autoSum a b c d else 0 := by
  simp only [blockGram, gsBlocks_transpose]
  fin_cases q <;> fin_cases r
  all_goals
    simp [gsBlocks, gsBlocksT, autoSum, Fin.sum_univ_four, circ_rev_mul_circ_rev,
      circ_rev_mul_circ_transpose_rev, circ_transpose_rev_mul_circ_rev,
      circ_transpose_rev_mul_circ_transpose_rev, circ_transpose_mul_circ_rev,
      circ_transpose_mul_circ_transpose_rev, circ_normal]
  all_goals try rw [circ_transpose_comm]
  all_goals try rw [circ_comm]
  all_goals try rw [circ_transpose_comm_transpose]
  all_goals abel

private def periodicCorrelation (x : C → ℤ) (t : C) : ℤ :=
  ∑ i : C, x i * x (i + t)

@[category API, AMS 15]
private lemma periodicCorrelation_neg (x : C → ℤ) (t : C) :
    periodicCorrelation x (-t) = periodicCorrelation x t := by
  rw [periodicCorrelation, periodicCorrelation,
    ← Equiv.sum_comp (Equiv.addRight t) (fun i : C => x i * x (i + -t))]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

@[category API, AMS 15]
private lemma circ_gram_apply (x : C → ℤ) (i j : C) :
    ((circ x).transpose * circ x) i j = periodicCorrelation x (i - j) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, circ, Matrix.circulant_apply, periodicCorrelation]
  rw [← Equiv.sum_comp (Equiv.addRight i)
    (fun k : C => x (k - i) * x (k - j))]
  apply Finset.sum_congr rfl
  intro k _
  congr 2 <;> simp [add_sub_assoc]

private def autoKernel (a b c d : C → ℤ) : C → ℤ :=
  fun t => periodicCorrelation a t + periodicCorrelation b t +
    periodicCorrelation c t + periodicCorrelation d t

@[category API, AMS 15]
private lemma autoSum_eq_circulant (a b c d : C → ℤ) :
    autoSum a b c d = Matrix.circulant (autoKernel a b c d) := by
  ext i j
  simp [autoSum, autoKernel, circ_gram_apply, Matrix.circulant_apply]

private def totalCorrelation (t : C) : ℤ :=
  ∑ q : Q, periodicCorrelation (seed q) t

@[category API, AMS 15]
private lemma totalCorrelation_neg (t : C) : totalCorrelation (-t) = totalCorrelation t := by
  simp [totalCorrelation, periodicCorrelation_neg]

@[category test, AMS 15]
private lemma totalCorrelation_zero : totalCorrelation 0 = 664 := by
  decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_1_5 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 1, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_5_9 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 5, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_9_13 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 9, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_13_17 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 13, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_17_21 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 17, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_21_25 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 21, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_25_29 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 25, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_29_33 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 29, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_33_37 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 33, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_37_41 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 37, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_41_45 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 41, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_45_49 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 45, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_49_53 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 49, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_53_57 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 53, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_57_61 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 57, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_61_65 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 61, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_65_69 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 65, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_69_73 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 69, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_73_77 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 73, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_77_81 :
    ∀ k : Fin 4, totalCorrelation ⟨k + 77, by omega⟩ = -4 := by decide +kernel

@[category test, AMS 15]
private lemma totalCorrelation_81_84 :
    ∀ k : Fin 3, totalCorrelation ⟨k + 81, by omega⟩ = -4 := by decide +kernel

@[category API, AMS 15]
private lemma totalCorrelation_of_mem (t : C) (lo len : ℕ) (hlo : lo ≤ t.val)
    (hhi : t.val < lo + len) (hbound : lo + len ≤ 166)
    (hcert : ∀ k : Fin len, totalCorrelation ⟨k + lo, by omega⟩ = -4) :
    totalCorrelation t = -4 := by
  let k : Fin len := ⟨t.val - lo, by omega⟩
  have h := hcert k
  simpa only [k, show t.val - lo + lo = t.val by omega] using h

@[category API, AMS 15]
private lemma totalCorrelation_first_half (t : C) (hlo : 1 ≤ t.val) (hhi : t.val < 84) :
    totalCorrelation t = -4 := by
  by_cases h5 : t.val < 5
  · exact totalCorrelation_of_mem t 1 4 hlo (by omega) (by omega) totalCorrelation_1_5
  by_cases h9 : t.val < 9
  · exact totalCorrelation_of_mem t 5 4 (by omega) (by omega) (by omega) totalCorrelation_5_9
  by_cases h13 : t.val < 13
  · exact totalCorrelation_of_mem t 9 4 (by omega) (by omega) (by omega) totalCorrelation_9_13
  by_cases h17 : t.val < 17
  · exact totalCorrelation_of_mem t 13 4 (by omega) (by omega) (by omega)
      totalCorrelation_13_17
  by_cases h21 : t.val < 21
  · exact totalCorrelation_of_mem t 17 4 (by omega) (by omega) (by omega)
      totalCorrelation_17_21
  by_cases h25 : t.val < 25
  · exact totalCorrelation_of_mem t 21 4 (by omega) (by omega) (by omega)
      totalCorrelation_21_25
  by_cases h29 : t.val < 29
  · exact totalCorrelation_of_mem t 25 4 (by omega) (by omega) (by omega)
      totalCorrelation_25_29
  by_cases h33 : t.val < 33
  · exact totalCorrelation_of_mem t 29 4 (by omega) (by omega) (by omega)
      totalCorrelation_29_33
  by_cases h37 : t.val < 37
  · exact totalCorrelation_of_mem t 33 4 (by omega) (by omega) (by omega)
      totalCorrelation_33_37
  by_cases h41 : t.val < 41
  · exact totalCorrelation_of_mem t 37 4 (by omega) (by omega) (by omega)
      totalCorrelation_37_41
  by_cases h45 : t.val < 45
  · exact totalCorrelation_of_mem t 41 4 (by omega) (by omega) (by omega)
      totalCorrelation_41_45
  by_cases h49 : t.val < 49
  · exact totalCorrelation_of_mem t 45 4 (by omega) (by omega) (by omega)
      totalCorrelation_45_49
  by_cases h53 : t.val < 53
  · exact totalCorrelation_of_mem t 49 4 (by omega) (by omega) (by omega)
      totalCorrelation_49_53
  by_cases h57 : t.val < 57
  · exact totalCorrelation_of_mem t 53 4 (by omega) (by omega) (by omega)
      totalCorrelation_53_57
  by_cases h61 : t.val < 61
  · exact totalCorrelation_of_mem t 57 4 (by omega) (by omega) (by omega)
      totalCorrelation_57_61
  by_cases h65 : t.val < 65
  · exact totalCorrelation_of_mem t 61 4 (by omega) (by omega) (by omega)
      totalCorrelation_61_65
  by_cases h69 : t.val < 69
  · exact totalCorrelation_of_mem t 65 4 (by omega) (by omega) (by omega)
      totalCorrelation_65_69
  by_cases h73 : t.val < 73
  · exact totalCorrelation_of_mem t 69 4 (by omega) (by omega) (by omega)
      totalCorrelation_69_73
  by_cases h77 : t.val < 77
  · exact totalCorrelation_of_mem t 73 4 (by omega) (by omega) (by omega)
      totalCorrelation_73_77
  by_cases h81 : t.val < 81
  · exact totalCorrelation_of_mem t 77 4 (by omega) (by omega) (by omega)
      totalCorrelation_77_81
  exact totalCorrelation_of_mem t 81 3 (by omega) (by omega) (by omega)
    totalCorrelation_81_84

@[category API, AMS 15]
private lemma totalCorrelation_nonzero (t : C) (ht : t ≠ 0) : totalCorrelation t = -4 := by
  have ht0 : 1 ≤ t.val := by
    by_contra h
    have : t.val = 0 := by omega
    exact ht (Fin.ext this)
  by_cases h84 : t.val < 84
  · exact totalCorrelation_first_half t ht0 h84
  · rw [← totalCorrelation_neg t]
    have hneg : (-t).val = 166 - t.val := by
      rw [Fin.val_neg']
      exact Nat.mod_eq_of_lt (by omega)
    apply totalCorrelation_first_half (-t) <;> omega

@[category API, AMS 15]
private lemma autoKernel_seed (t : C) :
    autoKernel (seed 0) (seed 1) (seed 2) (seed 3) t = totalCorrelation t := by
  simp [autoKernel, totalCorrelation, Fin.sum_univ_four]

@[category API, AMS 15]
private lemma autoSum_seed_apply (i j : C) :
    autoSum (seed 0) (seed 1) (seed 2) (seed 3) i j =
      if i = j then 664 else -4 := by
  rw [autoSum_eq_circulant, Matrix.circulant_apply, autoKernel_seed]
  by_cases hij : i = j
  · subst j
    simp [totalCorrelation_zero]
  · rw [if_neg hij, totalCorrelation_nonzero]
    intro h
    apply hij
    exact sub_eq_zero.mp h

@[category API, AMS 15]
private lemma circ_col_sum (x : C → ℤ) (j : C) : ∑ i, circ x i j = ∑ i, x i := by
  exact Equiv.sum_comp (Equiv.subRight j) x

@[category API, AMS 15]
private lemma circ_transpose_col_sum (x : C → ℤ) (j : C) :
    ∑ i, (circ x).transpose i j = ∑ i, x i := by
  exact Equiv.sum_comp (Equiv.subLeft j) x

@[category API, AMS 15]
private lemma circ_rev_col_sum (x : C → ℤ) (j : C) :
    ∑ i, (circ x * rev) i j = ∑ i, x i := by
  rw [rev, Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  exact circ_col_sum x ((Equiv.neg C).symm j)

@[category API, AMS 15]
private lemma circ_transpose_rev_col_sum (x : C → ℤ) (j : C) :
    ∑ i, ((circ x).transpose * rev) i j = ∑ i, x i := by
  rw [rev, Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  exact circ_transpose_col_sum x ((Equiv.neg C).symm j)

private def gsBlockSums (sa sb sc sd : ℤ) : Matrix Q Q ℤ :=
  !![sa, sb, sc, sd;
     -sb, sa, sd, -sc;
     -sc, -sd, sa, sb;
     -sd, sc, -sb, sa]

@[category API, AMS 15]
private lemma gsBlocks_col_sum_general (a b c d : C → ℤ) (p q : Q) (j : C) :
    ∑ i, gsBlocks a b c d p q i j =
      gsBlockSums (∑ i, a i) (∑ i, b i) (∑ i, c i) (∑ i, d i) p q := by
  fin_cases p <;> fin_cases q
  · change (∑ i, circ a i j) = ∑ i, a i
    exact circ_col_sum a j
  · change (∑ i, (circ b * rev) i j) = ∑ i, b i
    exact circ_rev_col_sum b j
  · change (∑ i, (circ c * rev) i j) = ∑ i, c i
    exact circ_rev_col_sum c j
  · change (∑ i, (circ d * rev) i j) = ∑ i, d i
    exact circ_rev_col_sum d j
  · change (∑ i, -(circ b * rev) i j) = -(∑ i, b i)
    rw [Finset.sum_neg_distrib, circ_rev_col_sum]
  · change (∑ i, circ a i j) = ∑ i, a i
    exact circ_col_sum a j
  · change (∑ i, ((circ d).transpose * rev) i j) = ∑ i, d i
    exact circ_transpose_rev_col_sum d j
  · change (∑ i, -((circ c).transpose * rev) i j) = -(∑ i, c i)
    rw [Finset.sum_neg_distrib, circ_transpose_rev_col_sum]
  · change (∑ i, -(circ c * rev) i j) = -(∑ i, c i)
    rw [Finset.sum_neg_distrib, circ_rev_col_sum]
  · change (∑ i, -((circ d).transpose * rev) i j) = -(∑ i, d i)
    rw [Finset.sum_neg_distrib, circ_transpose_rev_col_sum]
  · change (∑ i, circ a i j) = ∑ i, a i
    exact circ_col_sum a j
  · change (∑ i, ((circ b).transpose * rev) i j) = ∑ i, b i
    exact circ_transpose_rev_col_sum b j
  · change (∑ i, -(circ d * rev) i j) = -(∑ i, d i)
    rw [Finset.sum_neg_distrib, circ_rev_col_sum]
  · change (∑ i, ((circ c).transpose * rev) i j) = ∑ i, c i
    exact circ_transpose_rev_col_sum c j
  · change (∑ i, -((circ b).transpose * rev) i j) = -(∑ i, b i)
    rw [Finset.sum_neg_distrib, circ_transpose_rev_col_sum]
  · change (∑ i, circ a i j) = ∑ i, a i
    exact circ_col_sum a j

@[category API, AMS 15]
private lemma seed_zero_sum : ∑ i, seed 0 i = 2 := by simpa using seed_sum 0

@[category API, AMS 15]
private lemma seed_one_sum : ∑ i, seed 1 i = 0 := by simpa using seed_sum 1

@[category API, AMS 15]
private lemma seed_two_sum : ∑ i, seed 2 i = 0 := by simpa using seed_sum 2

@[category API, AMS 15]
private lemma seed_three_sum : ∑ i, seed 3 i = 0 := by simpa using seed_sum 3

@[category API, AMS 15]
private lemma gsBlockSums_seed : gsBlockSums 2 0 0 0 = (2 : Matrix Q Q ℤ) := by
  ext p q
  fin_cases p <;> fin_cases q <;> norm_num [gsBlockSums, Matrix.ofNat_apply]

@[category API, AMS 15]
private lemma gsBlocks_col_sum (p q : Q) (j : C) :
    ∑ i, gsBlocks (seed 0) (seed 1) (seed 2) (seed 3) p q i j =
      if p = q then 2 else 0 := by
  rw [gsBlocks_col_sum_general, seed_zero_sum, seed_one_sum, seed_two_sum,
    seed_three_sum, gsBlockSums_seed]
  simp [Matrix.ofNat_apply]

private def coreMatrix : Matrix (Q × C) (Q × C) ℤ := fun i j =>
  gsBlocks (seed 0) (seed 1) (seed 2) (seed 3) i.1 j.1 i.2 j.2

@[category API, AMS 15]
private lemma core_gram_apply (q r : Q) (i j : C) :
    (coreMatrix.transpose * coreMatrix) (q, i) (r, j) =
      if q = r then autoSum (seed 0) (seed 1) (seed 2) (seed 3) i j else 0 := by
  by_cases hqr : q = r
  · subst r
    rw [if_pos rfl, Matrix.mul_apply, Fintype.sum_prod_type]
    have h := congrArg (fun M : Matrix C C ℤ => M i j)
      (blockGram_all (seed 0) (seed 1) (seed 2) (seed 3) q q)
    rw [if_pos rfl] at h
    simpa only [blockGram, Finset.sum_apply, Matrix.mul_apply, Matrix.transpose_apply]
      using h
  · rw [if_neg hqr, Matrix.mul_apply, Fintype.sum_prod_type]
    have h := congrArg (fun M : Matrix C C ℤ => M i j)
      (blockGram_all (seed 0) (seed 1) (seed 2) (seed 3) q r)
    rw [if_neg hqr] at h
    simpa only [blockGram, Finset.sum_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.zero_apply] using h

private def border : Matrix Q Q ℤ :=
  !![-1, 1, 1, -1;
      1, -1, 1, -1;
      1, 1, -1, -1;
      -1, -1, -1, -1]

private def top : Matrix Q Q ℤ :=
  !![1, -1, -1, 1;
     1, -1, 1, -1;
     1, 1, -1, -1;
     -1, -1, -1, -1]

private def left : Matrix Q Q ℤ :=
  !![-1, -1, -1, 1;
     -1, -1, 1, -1;
     -1, 1, -1, -1;
     1, -1, -1, -1]

@[category test, AMS 15]
private lemma border_gram : border.transpose * border = (4 : Matrix Q Q ℤ) := by
  decide +kernel

@[category test, AMS 15]
private lemma top_gram : top.transpose * top = (4 : Matrix Q Q ℤ) := by
  decide +kernel

@[category test, AMS 15]
private lemma left_gram : left.transpose * left = (4 : Matrix Q Q ℤ) := by
  decide +kernel

@[category test, AMS 15]
private lemma border_cross : border.transpose * top + 2 • left.transpose = 0 := by
  decide +kernel

private def topExpanded : Matrix Q (Q × C) ℤ := fun i j => top i j.1

private def leftExpanded : Matrix (Q × C) Q ℤ := fun i j => left i.1 j

private def borderedMatrix : Matrix (Q ⊕ (Q × C)) (Q ⊕ (Q × C)) ℤ :=
  Matrix.fromBlocks border topExpanded leftExpanded coreMatrix

private def IsSign (z : ℤ) : Prop := z = 1 ∨ z = -1

@[category API, AMS 15]
private lemma seed_sign (q : Q) (i : C) : IsSign (seed q i) := by
  simp only [IsSign, seed]
  split <;> simp

@[category API, AMS 15]
private lemma sign_neg {z : ℤ} (hz : IsSign z) : IsSign (-z) := by
  rcases hz with rfl | rfl <;> simp [IsSign]

@[category API, AMS 15]
private lemma circ_seed_sign (q : Q) (i j : C) : IsSign (circ (seed q) i j) := by
  exact seed_sign q (i - j)

@[category API, AMS 15]
private lemma circ_transpose_seed_sign (q : Q) (i j : C) :
    IsSign ((circ (seed q)).transpose i j) := by
  exact seed_sign q (j - i)

@[category API, AMS 15]
private lemma circ_rev_apply (x : C → ℤ) (i j : C) :
    (circ x * rev) i j = circ x i ((Equiv.neg C).symm j) := by
  rw [rev, Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  rfl

@[category API, AMS 15]
private lemma circ_rev_seed_sign (q : Q) (i j : C) :
    IsSign ((circ (seed q) * rev) i j) := by
  rw [circ_rev_apply]
  exact circ_seed_sign q i ((Equiv.neg C).symm j)

@[category API, AMS 15]
private lemma circ_transpose_rev_seed_sign (q : Q) (i j : C) :
    IsSign (((circ (seed q)).transpose * rev) i j) := by
  rw [rev, Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  exact circ_transpose_seed_sign q i ((Equiv.neg C).symm j)

@[category API, AMS 15]
private lemma coreMatrix_sign (i j : Q × C) : IsSign (coreMatrix i j) := by
  rcases i with ⟨p, i⟩
  rcases j with ⟨q, j⟩
  fin_cases p <;> fin_cases q <;> simp only [coreMatrix, gsBlocks]
  all_goals first
    | exact circ_seed_sign 0 i j
    | exact circ_rev_seed_sign 1 i j
    | exact circ_rev_seed_sign 2 i j
    | exact circ_rev_seed_sign 3 i j
    | exact sign_neg (circ_rev_seed_sign 1 i j)
    | exact sign_neg (circ_rev_seed_sign 2 i j)
    | exact sign_neg (circ_rev_seed_sign 3 i j)
    | exact circ_transpose_rev_seed_sign 1 i j
    | exact circ_transpose_rev_seed_sign 2 i j
    | exact circ_transpose_rev_seed_sign 3 i j
    | exact sign_neg (circ_transpose_rev_seed_sign 1 i j)
    | exact sign_neg (circ_transpose_rev_seed_sign 2 i j)
    | exact sign_neg (circ_transpose_rev_seed_sign 3 i j)

@[category API, AMS 15]
private lemma borderedMatrix_sign (i j : Q ⊕ (Q × C)) : IsSign (borderedMatrix i j) := by
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j <;> simp [borderedMatrix, border, Matrix.fromBlocks, IsSign]
  · fin_cases i <;> rcases j with ⟨q, _j⟩ <;> fin_cases q <;>
      simp [borderedMatrix, topExpanded, top, Matrix.fromBlocks, IsSign]
  · rcases i with ⟨p, _i⟩
    fin_cases p <;> fin_cases j <;>
      simp [borderedMatrix, leftExpanded, left, Matrix.fromBlocks, IsSign]
  · exact coreMatrix_sign i j

@[category API, AMS 15]
private lemma leftExpanded_gram :
    leftExpanded.transpose * leftExpanded = (664 : Matrix Q Q ℤ) := by
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  change (∑ p : Q, ∑ _k : C, left p i * left p j) = _
  calc
    (∑ p : Q, ∑ _k : C, left p i * left p j) =
        166 * ∑ p : Q, left p i * left p j := by
      simp [Finset.mul_sum]
    _ = 166 * (left.transpose * left) i j := by simp [Matrix.mul_apply]
    _ = (664 : Matrix Q Q ℤ) i j := by rw [left_gram]; simp [Matrix.ofNat_apply]

@[category API, AMS 15]
private lemma topExpanded_gram_apply (q r : Q) (i j : C) :
    (topExpanded.transpose * topExpanded) (q, i) (r, j) =
      if q = r then 4 else 0 := by
  change (∑ x, top x q * top x r) = _
  calc
    (∑ x, top x q * top x r) = (top.transpose * top) q r := by
      rfl
    _ = _ := by rw [top_gram]; simp [Matrix.ofNat_apply]

@[category API, AMS 15]
private lemma left_core_mul_apply (j : Q) (q : Q) (b : C) :
    (leftExpanded.transpose * coreMatrix) j (q, b) = 2 * left.transpose j q := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  change (∑ p : Q, ∑ k : C, left p j *
    gsBlocks (seed 0) (seed 1) (seed 2) (seed 3) p q k b) = _
  simp_rw [← Finset.mul_sum, gsBlocks_col_sum]
  simp [Matrix.transpose_apply]
  ring

@[category API, AMS 15]
private lemma boundary_gram :
    border.transpose * border + leftExpanded.transpose * leftExpanded =
      (668 : Matrix Q Q ℤ) := by
  rw [border_gram, leftExpanded_gram]
  ext i j
  by_cases hij : i = j <;> simp [hij, Matrix.ofNat_apply]

@[category API, AMS 15]
private lemma core_border_gram :
    topExpanded.transpose * topExpanded + coreMatrix.transpose * coreMatrix =
      (668 : Matrix (Q × C) (Q × C) ℤ) := by
  ext ⟨q, i⟩ ⟨r, j⟩
  rw [Matrix.add_apply, topExpanded_gram_apply, core_gram_apply]
  by_cases hqr : q = r
  · subst r
    rw [if_pos rfl, autoSum_seed_apply]
    by_cases hij : i = j
    · subst j
      simp [Matrix.ofNat_apply]
    · simp [hij, Matrix.ofNat_apply]
  · simp [hqr, Matrix.ofNat_apply]

@[category API, AMS 15]
private lemma border_core_cross :
    border.transpose * topExpanded + leftExpanded.transpose * coreMatrix = 0 := by
  ext j ⟨q, b⟩
  rw [Matrix.add_apply, left_core_mul_apply]
  have h := congrArg (fun M : Matrix Q Q ℤ => M j q) border_cross
  simpa only [topExpanded, Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] using h

@[category API, AMS 15]
private lemma core_border_cross :
    topExpanded.transpose * border + coreMatrix.transpose * leftExpanded = 0 := by
  have h := congrArg Matrix.transpose border_core_cross
  simpa only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_zero] using h

@[category API, AMS 15]
private lemma borderedMatrix_gram :
    borderedMatrix.transpose * borderedMatrix =
      (668 : Matrix (Q ⊕ (Q × C)) (Q ⊕ (Q × C)) ℤ) := by
  rw [borderedMatrix, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    boundary_gram, border_core_cross, core_border_cross, core_border_gram]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.ofNat_apply]

private def indexEquiv : (Q ⊕ (Q × C)) ≃ Fin 668 :=
  (Equiv.sumCongr (Equiv.refl Q) finProdFinEquiv).trans finSumFinEquiv

/-- The order-668 Wallis--Whiteman matrix over the integers. -/
def H668Int : Matrix (Fin 668) (Fin 668) ℤ :=
  Matrix.reindex indexEquiv indexEquiv borderedMatrix

/-- Every entry of `H668Int` is $+1$ or $-1$. -/
@[category test, AMS 15]
theorem H668Int_sign (i j : Fin 668) : H668Int i j = 1 ∨ H668Int i j = -1 := by
  exact borderedMatrix_sign (indexEquiv.symm i) (indexEquiv.symm j)

set_option maxRecDepth 10000 in
/-- The columns of `H668Int` are pairwise orthogonal and have squared norm 668. -/
@[category test, AMS 15]
theorem H668Int_gram :
    H668Int.transpose * H668Int = (668 : Matrix (Fin 668) (Fin 668) ℤ) := by
  change (Matrix.reindex indexEquiv indexEquiv borderedMatrix).transpose *
    Matrix.reindex indexEquiv indexEquiv borderedMatrix = _
  rw [Matrix.transpose_reindex]
  rw [← Matrix.reindexAlgEquiv_apply ℤ ℤ, ← Matrix.reindexAlgEquiv_apply ℤ ℤ,
    ← map_mul, borderedMatrix_gram]
  rw [Matrix.reindexAlgEquiv_apply]
  ext i j
  simp [Matrix.reindex, Matrix.ofNat_apply]

end Hadamard
