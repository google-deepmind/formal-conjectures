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
module

public import Mathlib.Data.Int.GCD
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.NumberTheory.Divisors

import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Coset representatives for the Hecke operators at level one

For `n ≠ 0`, the set of integer `2 × 2` matrices of determinant `n` is a finite union of right
cosets `SL(2, ℤ) · A`, and the upper-triangular matrices `!![a, b; 0, d]` with `a * d = n` and
`0 ≤ b < d` represent these cosets, each exactly once (Serre, *A course in arithmetic*, Chapter
VII, §5.2, Lemma 2). This is the combinatorial input to the modularity of the Hecke operators
`T_n`: right multiplication by an element of `SL(2, ℤ)` permutes the cosets, hence the
representatives up to left multiplication by `SL(2, ℤ)`.

This file proves that statement in the following explicit form.

* `hermiteReduce A` is the triple `((a, d), b)` of the representative of the coset of `A`, and
  `hermiteTransform A` is the matrix of determinant `1` with
  `hermiteTransform A * A = !![a, b; 0, d]` (`hermiteTransform_mul`, `det_hermiteTransform`).
  The reduction is Bezout's identity on the first column followed by a shear reducing the
  top-right entry modulo `d`.
* The representative is unique (`eq_of_mul_heckeMatrixInt_eq`), so `hermiteReduce` is constant
  on cosets (`hermiteReduce_mul_left`) and fixes the representatives
  (`hermiteReduce_heckeMatrixInt`).

## Main definitions

* `ModularForm.heckeIndex n`: the finset of triples `((a, d), b)` with `a * d = n` and `b < d`,
  the index set of the Hecke operator `T_n`.
* `ModularForm.heckeMatrixInt p`: the integer matrix `!![a, b; 0, d]` labelled by `p`.
* `ModularForm.hermiteReduce A`, `ModularForm.hermiteTransform A`: the reduction of an integer
  matrix `A` of positive determinant to its representative.

## Main results

* `ModularForm.sum_heckeIndex`: a sum over `heckeIndex n` is the double sum over `a * d = n`
  and `b < d`.
* `ModularForm.hermiteTransform_mul`, `ModularForm.det_hermiteTransform`,
  `ModularForm.hermiteReduce_mem_heckeIndex`: existence of the representative.
* `ModularForm.eq_of_mul_heckeMatrixInt_eq`: uniqueness of the representative.
* `ModularForm.hermiteReduce_heckeMatrixInt`, `ModularForm.hermiteReduce_mul_left`: the
  reduction is a retraction onto the representatives, constant on cosets.

## References

* J.-P. Serre, *A course in arithmetic*, Chapter VII, §5.2, Lemma 2.
* F. Diamond and J. Shurman, *A first course in modular forms*, §5.2–5.3.
-/

open Matrix Finset

namespace ModularForm

/-! ### The index set of `T_n` -/

/-- The index set of the Hecke operator `T_n`: the triples `((a, d), b)` of natural numbers with
`a * d = n` and `b < d`. The triple `((a, d), b)` labels the matrix `!![a, b; 0, d]`.

For `n = 0` this is empty, since `Nat.divisorsAntidiagonal 0 = ∅`. -/
def heckeIndex (n : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (n.divisorsAntidiagonal ×ˢ range n).filter fun p ↦ p.2 < p.1.2

/-- Membership in the index set: `((a, d), b)` indexes `T_n` exactly when `a d = n` (so `n ≠ 0`)
and `0 ≤ b < d`. -/
@[simp]
lemma mem_heckeIndex {n : ℕ} {p : (ℕ × ℕ) × ℕ} :
    p ∈ heckeIndex n ↔ p.1.1 * p.1.2 = n ∧ n ≠ 0 ∧ p.2 < p.1.2 := by
  obtain ⟨⟨a, d⟩, b⟩ := p
  simp only [heckeIndex, mem_filter, mem_product, Nat.mem_divisorsAntidiagonal, mem_range]
  refine ⟨fun ⟨⟨⟨h, hn⟩, _⟩, hb⟩ ↦ ⟨h, hn, hb⟩, fun ⟨h, hn, hb⟩ ↦ ⟨⟨⟨h, hn⟩, ?_⟩, hb⟩⟩
  subst h
  exact hb.trans_le (Nat.le_mul_of_pos_left d (Nat.pos_of_ne_zero (left_ne_zero_of_mul hn)))

/-- A sum over the index set of `T_n` is the double sum over `a * d = n` and `b < d`. -/
lemma sum_heckeIndex {M : Type*} [AddCommMonoid M] (n : ℕ) (F : (ℕ × ℕ) × ℕ → M) :
    ∑ p ∈ heckeIndex n, F p = ∑ x ∈ n.divisorsAntidiagonal, ∑ b ∈ range x.2, F (x, b) := by
  rw [heckeIndex, sum_filter, sum_product]
  refine sum_congr rfl fun x hx ↦ ?_
  obtain ⟨h, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have hle : x.2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Dvd.intro_left _ h)
  rw [← sum_filter]
  congr 1
  ext b
  simp only [mem_filter, mem_range]
  omega

/-- The integer matrix `!![a, b; 0, d]` labelled by the triple `((a, d), b)`. -/
def heckeMatrixInt (p : (ℕ × ℕ) × ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(p.1.1 : ℤ), p.2; 0, p.1.2]

/-- The determinant of the representative `!![a, b; 0, d]` is `a d`. -/
@[simp]
lemma det_heckeMatrixInt (p : (ℕ × ℕ) × ℕ) : (heckeMatrixInt p).det = p.1.1 * p.1.2 := by
  simp [heckeMatrixInt, det_fin_two_of]

/-- A representative indexing `T_n` has determinant exactly `n`. -/
lemma det_heckeMatrixInt_of_mem {n : ℕ} {p : (ℕ × ℕ) × ℕ} (hp : p ∈ heckeIndex n) :
    (heckeMatrixInt p).det = n := by
  simp [← (mem_heckeIndex.mp hp).1]

/-- A representative indexing `T_n` has positive determinant, since `n ≠ 0`. -/
lemma det_heckeMatrixInt_pos {n : ℕ} {p : (ℕ × ℕ) × ℕ} (hp : p ∈ heckeIndex n) :
    0 < (heckeMatrixInt p).det := by
  simpa [det_heckeMatrixInt_of_mem hp] using Nat.pos_of_ne_zero (mem_heckeIndex.mp hp).2.1

/-! ### Uniqueness of the representative -/

/-- Two naturals below `d` differing by an integer multiple of `d` are equal. -/
private lemma eq_of_add_mul_eq_of_lt {b b' d : ℕ} {c : ℤ} (hb : b < d) (hb' : b' < d)
    (h : (b : ℤ) + c * d = b') : b = b' := by
  have : (b' : ℤ) % d = b % d := by rw [← h, Int.add_mul_emod_self_right]
  rwa [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega),
    Nat.cast_inj, eq_comm] at this

/-- The matrix half of uniqueness: a determinant-one matrix taking one normalised representative
to another fixes `a` and `d` and shifts `b` by a multiple of `d`. The lower-left entry of `δ`
vanishes because `a > 0`, and its diagonal is `(1, 1)` because `(-1, -1)` would force `a'` to be
negative. -/
private lemma exists_add_mul_eq_of_mul_heckeMatrixInt_eq {n : ℕ} {p q : (ℕ × ℕ) × ℕ}
    {δ : Matrix (Fin 2) (Fin 2) ℤ} (hδ : δ.det = 1) (hp : p ∈ heckeIndex n)
    (h : δ * heckeMatrixInt p = heckeMatrixInt q) :
    p.1.1 = q.1.1 ∧ p.1.2 = q.1.2 ∧ ∃ c : ℤ, (p.2 : ℤ) + c * p.1.2 = q.2 := by
  obtain ⟨⟨a, d⟩, b⟩ := p
  obtain ⟨⟨a', d'⟩, b'⟩ := q
  obtain ⟨hp, hn, -⟩ := mem_heckeIndex.mp hp
  have ha : 0 < a := Nat.pos_of_ne_zero (left_ne_zero_of_mul (hp ▸ hn))
  rw [det_fin_two] at hδ
  -- the lower-left entry of `δ` vanishes since `a > 0`
  simp [heckeMatrixInt, ← Matrix.ext_iff, Fin.forall_fin_two, mul_apply, Fin.sum_univ_two,
    ha.ne'] at h
  obtain ⟨⟨h00, h01⟩, hR, h11⟩ := h
  simp only [hR, mul_zero, sub_zero, zero_mul, zero_add] at hδ h11
  -- the diagonal of `δ` is `1`: `-1` is excluded by positivity of `a` and `a'`
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hδ with ⟨hP, hS⟩ | ⟨hP, hS⟩
  · simp only [hP, hS, one_mul] at h00 h01 h11
    exact ⟨by exact_mod_cast h00, by exact_mod_cast h11, δ 0 1, h01⟩
  · rw [hP] at h00; omega

/-- **Uniqueness of the representative.** Two representatives `!![a, b; 0, d]` and
`!![a', b'; 0, d']` of the same determinant `n`, with `b < d` and `b' < d'`, that differ by left
multiplication by a matrix of determinant `1` are equal. -/
theorem eq_of_mul_heckeMatrixInt_eq {n : ℕ} {p q : (ℕ × ℕ) × ℕ}
    {δ : Matrix (Fin 2) (Fin 2) ℤ} (hδ : δ.det = 1) (hp : p ∈ heckeIndex n)
    (hq : q ∈ heckeIndex n) (h : δ * heckeMatrixInt p = heckeMatrixInt q) : p = q := by
  obtain ⟨haa, hdd, c, hc⟩ := exists_add_mul_eq_of_mul_heckeMatrixInt_eq hδ hp h
  exact Prod.ext (Prod.ext haa hdd)
    (eq_of_add_mul_eq_of_lt (mem_heckeIndex.mp hp).2.2 (hdd ▸ (mem_heckeIndex.mp hq).2.2) hc)

/-! ### Existence of the representative: Bezout reduction -/

/-- The gcd of the first column of `A`. -/
def hermiteGcd (A : Matrix (Fin 2) (Fin 2) ℤ) : ℕ := Int.gcd (A 0 0) (A 1 0)

/-- The Bezout step: for `A = !![a, b; c, d]` with `g = gcd a c = x * a + y * c`, the matrix
`!![x, y; -c / g, a / g]` of determinant `1`, which kills the lower-left entry of `A`. -/
def bezoutStep (A : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![Int.gcdA (A 0 0) (A 1 0), Int.gcdB (A 0 0) (A 1 0);
    -(A 1 0 / hermiteGcd A), A 0 0 / hermiteGcd A]

/-- The top-right entry of `bezoutStep A * A`. -/
def hermiteB (A : Matrix (Fin 2) (Fin 2) ℤ) : ℤ :=
  Int.gcdA (A 0 0) (A 1 0) * A 0 1 + Int.gcdB (A 0 0) (A 1 0) * A 1 1

/-- The bottom-right entry of `bezoutStep A * A`, namely `det A / gcd (A 0 0) (A 1 0)`. -/
def hermiteD (A : Matrix (Fin 2) (Fin 2) ℤ) : ℤ := A.det / hermiteGcd A

/-- The representative `((a, d), b)` of the coset `SL(2, ℤ) · A`: `a` is the gcd of the first
column, `d = det A / a`, and `b` is the top-right entry after the Bezout step, reduced modulo `d`.
For `det A ≤ 0` the value is junk. -/
def hermiteReduce (A : Matrix (Fin 2) (Fin 2) ℤ) : (ℕ × ℕ) × ℕ :=
  ((hermiteGcd A, (hermiteD A).toNat), (hermiteB A % hermiteD A).toNat)

/-- The matrix carrying `A` to its representative, `hermiteTransform A * A = !![a, b; 0, d]`: the
Bezout step followed by the shear reducing the top-right entry modulo `d`. Its determinant is `1`
when `det A ≠ 0` (`det_hermiteTransform`). -/
def hermiteTransform (A : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, -(hermiteB A / hermiteD A); 0, 1] * bezoutStep A

variable {A : Matrix (Fin 2) (Fin 2) ℤ}

/-- A nonsingular matrix has a nonzero first column, hence nonzero first-column gcd. -/
lemma hermiteGcd_ne_zero (hA : A.det ≠ 0) : hermiteGcd A ≠ 0 := fun h ↦ hA <| by
  obtain ⟨h0, h1⟩ := Int.gcd_eq_zero_iff.mp h
  simp [det_fin_two, h0, h1]

/-- The gcd of the first column divides the determinant. -/
lemma hermiteGcd_dvd_det : (hermiteGcd A : ℤ) ∣ A.det := by
  rw [det_fin_two]
  exact ((Int.gcd_dvd_left _ _).mul_right _).sub ((Int.gcd_dvd_right _ _).mul_left _)

/-- The division defining `hermiteD` is exact: `g * (det A / g) = det A`. -/
lemma hermiteGcd_mul_hermiteD : (hermiteGcd A : ℤ) * hermiteD A = A.det :=
  Int.mul_ediv_cancel' hermiteGcd_dvd_det

/-- A matrix of positive determinant has positive `hermiteD`, the lower-right entry of its
Hermite form. -/
lemma hermiteD_pos (hA : 0 < A.det) : 0 < hermiteD A :=
  Int.ediv_pos_of_pos_of_dvd hA (Int.natCast_nonneg _) hermiteGcd_dvd_det

/-- The Bezout step brings `A` to upper-triangular form. -/
lemma bezoutStep_mul (hA : A.det ≠ 0) :
    bezoutStep A * A = !![(hermiteGcd A : ℤ), hermiteB A; 0, hermiteD A] := by
  have hg : (hermiteGcd A : ℤ) ≠ 0 := by exact_mod_cast hermiteGcd_ne_zero hA
  have hbez : (hermiteGcd A : ℤ) = A 0 0 * Int.gcdA (A 0 0) (A 1 0) +
      A 1 0 * Int.gcdB (A 0 0) (A 1 0) := Int.gcd_eq_gcd_ab _ _
  obtain ⟨a₁, ha₁⟩ : (hermiteGcd A : ℤ) ∣ A 0 0 := Int.gcd_dvd_left _ _
  obtain ⟨c₁, hc₁⟩ : (hermiteGcd A : ℤ) ∣ A 1 0 := Int.gcd_dvd_right _ _
  have hda : A 0 0 / hermiteGcd A = a₁ := by rw [ha₁, Int.mul_ediv_cancel_left _ hg]
  have hdc : A 1 0 / hermiteGcd A = c₁ := by rw [hc₁, Int.mul_ediv_cancel_left _ hg]
  have hdd : hermiteD A = a₁ * A 1 1 - c₁ * A 0 1 := by
    rw [hermiteD, det_fin_two, ha₁, hc₁, show (hermiteGcd A : ℤ) * a₁ * A 1 1 - A 0 1 *
      (hermiteGcd A * c₁) = hermiteGcd A * (a₁ * A 1 1 - c₁ * A 0 1) by ring,
      Int.mul_ediv_cancel_left _ hg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bezoutStep, Matrix.mul_apply, Fin.sum_univ_two, hermiteB, hda, hdc, hdd]
  · linear_combination -hbez
  · linear_combination (-c₁) * ha₁ + a₁ * hc₁
  · ring

/-- The Bezout step lies in `SL(2, ℤ)`: taking determinants in `bezoutStep_mul` gives
`det (bezoutStep A) * det A = g * (det A / g) = det A`. -/
lemma det_bezoutStep (hA : A.det ≠ 0) : (bezoutStep A).det = 1 :=
  mul_right_cancel₀ hA <| by
    rw [← det_mul, bezoutStep_mul hA, det_fin_two_of, mul_zero, sub_zero,
      hermiteGcd_mul_hermiteD, one_mul]

/-- The full reduction matrix lies in `SL(2, ℤ)`. -/
lemma det_hermiteTransform (hA : A.det ≠ 0) : (hermiteTransform A).det = 1 := by
  rw [hermiteTransform, det_mul, det_bezoutStep hA, det_fin_two_of]
  ring

/-- **Existence of the representative**: `hermiteTransform A * A = !![a, b; 0, d]` for the
triple `((a, d), b) = hermiteReduce A`. -/
theorem hermiteTransform_mul (hA : 0 < A.det) :
    hermiteTransform A * A = heckeMatrixInt (hermiteReduce A) := by
  have hd : 0 < hermiteD A := hermiteD_pos hA
  rw [hermiteTransform, mul_assoc, bezoutStep_mul hA.ne', heckeMatrixInt, hermiteReduce,
    mul_fin_two]
  simp only [Int.toNat_of_nonneg (Int.emod_nonneg _ hd.ne'), Int.toNat_of_nonneg hd.le]
  simp [Int.emod_def]
  ring

/-- `A` is recovered from its Hermite representative by inverting `hermiteTransform A`, whose
inverse is its adjugate because its determinant is `1`. -/
lemma eq_adjugate_hermiteTransform_mul (hA : 0 < A.det) :
    A = adjugate (hermiteTransform A) * heckeMatrixInt (hermiteReduce A) := by
  rw [← hermiteTransform_mul hA, ← mul_assoc, adjugate_mul, det_hermiteTransform hA.ne',
    one_smul, one_mul]

/-- The reduction of a matrix of positive determinant is a valid index triple for `det A`. -/
theorem hermiteReduce_mem_heckeIndex (hA : 0 < A.det) :
    hermiteReduce A ∈ heckeIndex A.det.toNat := by
  have hd : 0 < hermiteD A := hermiteD_pos hA
  rw [mem_heckeIndex, hermiteReduce]
  refine ⟨?_, by omega, (Int.toNat_lt_toNat hd).mpr (Int.emod_lt_of_pos _ hd)⟩
  zify
  rw [Int.toNat_of_nonneg hd.le, Int.toNat_of_nonneg hA.le]
  exact hermiteGcd_mul_hermiteD

/-- The reduction fixes the representatives. -/
theorem hermiteReduce_heckeMatrixInt {n : ℕ} {p : (ℕ × ℕ) × ℕ} (hp : p ∈ heckeIndex n) :
    hermiteReduce (heckeMatrixInt p) = p := by
  have hA : 0 < (heckeMatrixInt p).det := det_heckeMatrixInt_pos hp
  exact (eq_of_mul_heckeMatrixInt_eq (det_hermiteTransform hA.ne') hp
    (by simpa [det_heckeMatrixInt_of_mem hp] using hermiteReduce_mem_heckeIndex hA)
    (hermiteTransform_mul hA)).symm

/-- The reduction is constant on the cosets `SL(2, ℤ) · A`. -/
theorem hermiteReduce_mul_left {δ : Matrix (Fin 2) (Fin 2) ℤ} (hδ : δ.det = 1)
    (hA : 0 < A.det) : hermiteReduce (δ * A) = hermiteReduce A := by
  have hδA : 0 < (δ * A).det := by simpa [hδ] using hA
  have hmem₁ := hermiteReduce_mem_heckeIndex hδA
  rw [det_mul, hδ, one_mul] at hmem₁
  refine (eq_of_mul_heckeMatrixInt_eq (δ := hermiteTransform (δ * A) * δ *
    adjugate (hermiteTransform A)) ?_ (hermiteReduce_mem_heckeIndex hA) hmem₁ ?_).symm
  · simp [det_adjugate, det_hermiteTransform hδA.ne', hδ, det_hermiteTransform hA.ne']
  · rw [mul_assoc, ← eq_adjugate_hermiteTransform_mul hA, mul_assoc]
    exact hermiteTransform_mul hδA

end ModularForm

end
