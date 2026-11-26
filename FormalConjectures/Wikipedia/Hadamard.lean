/-
Copyright 2025 The Formal Conjectures Authors.

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

public import FormalConjecturesUtil

/-!
# Hadamard's conjecture

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Hadamard_matrix#Hadamard_conjecture)
 - [Tao's optimization constant 23a](https://teorth.github.io/optimizationproblems/constants/23a.html)
 - [Résolution d'une question relative aux déterminants](https://gallica.bnf.fr/ark:/12148/bpt6k486252g/f400.image.r) by *Jacques Hadamard*,  Bull. des sciences math., p.245, 1893
-/

@[expose] public section

namespace Hadamard

/--
A square matrix $M$ with $±1$-entries that satisfies the equality $|M| ≤ n^\frac{n}{2}$ is called a *Hadamard matrix*.
-/
def IsHadamard {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
    (∀ (i j : Fin n), M i j ∈ ({1, -1} : Finset ℝ)) ∧
    |M.det| = n ^ ((n : ℝ) / 2)

/--
Equivalently, a square matrix $M$ with $±1$-entries $|A| ≤ n^\frac{n}{2}.$ if it satisfies the equality
$M^TM = n \cdot 1$, where $1$ denotes the unit matrix.
-/
def IsHadamard' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
    (∀ (i j : Fin n), M i j ∈ ({1, -1} : Finset ℝ)) ∧
    M.transpose * M = ↑n

@[category test, AMS 15]
theorem isHadamard'_iff_abs_le_one_and_det_eq (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    IsHadamard' M ↔ (∀ i j, |M i j| ≤ 1) ∧ |M.det| = n ^ ((n : ℝ) / 2) := by
  have hdiag_n : Matrix.diagonal (fun _ => (n : ℝ)) = (n : Matrix (Fin n) (Fin n) ℝ) := rfl
  refine ⟨fun ⟨hM, h⟩ => ⟨fun i j => ?_, ?_⟩, fun ⟨hM, h⟩ => ?_⟩
  · rcases Finset.mem_insert.mp (hM i j) with h1 | h1 <;> simp_all
  · have hdet : M.det ^ 2 = (n : ℝ) ^ n := by
      simpa [Matrix.det_mul, Matrix.det_transpose, ← hdiag_n, sq] using congrArg Matrix.det h
    rw [← Real.sqrt_sq_eq_abs, hdet, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (Nat.cast_nonneg n), mul_one_div]
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨fun i => i.elim0, Subsingleton.elim _ _⟩
    · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have hH := Matrix.isHermitian_conjTranspose_mul_self M
      have he_nonneg := Matrix.eigenvalues_conjTranspose_mul_self_nonneg M
      have hsq : ∀ k i : Fin n, M k i * M k i ≤ 1 := fun k i => by nlinarith [abs_le.mp (hM k i)]
      have htrace_le : ∑ i, hH.eigenvalues i ≤ (n : ℝ) * n := by
        rw [show ∑ i, hH.eigenvalues i = ∑ i : Fin n, ∑ k : Fin n, M k i * M k i by
          simpa [Matrix.trace, Matrix.mul_apply] using hH.trace_eq_sum_eigenvalues.symm]
        simpa using Finset.sum_le_sum (s := Finset.univ) fun i _ =>
          Finset.sum_le_sum (s := Finset.univ) fun k _ => hsq k i
      have harith_le : ∑ i : Fin n, (n : ℝ)⁻¹ * hH.eigenvalues i ≤ n := by
        rw [← Finset.mul_sum]
        exact (mul_le_mul_of_nonneg_left htrace_le (inv_nonneg.mpr hn'.le)).trans_eq
          (inv_mul_cancel_left₀ hn'.ne' _)
      have hprod : ∏ i, hH.eigenvalues i = (n : ℝ) ^ n := by
        have hdp := hH.det_eq_prod_eigenvalues.symm
        rw [Matrix.det_mul, Matrix.det_conjTranspose, star_trivial, ← sq, ← sq_abs, h,
          ← Real.rpow_natCast, ← Real.rpow_mul hn'.le,
          show (n : ℝ) / 2 * (2 : ℕ) = (n : ℝ) by norm_num, Real.rpow_natCast] at hdp
        simpa using hdp
      have hgeom : ∏ i : Fin n, hH.eigenvalues i ^ (n : ℝ)⁻¹ = n := by
        rw [Real.finsetProd_rpow _ _ (fun i _ => he_nonneg i), hprod, ← Real.rpow_natCast,
          ← Real.rpow_mul hn'.le, mul_inv_cancel₀ hn'.ne', Real.rpow_one]
      have harith : ∑ i : Fin n, (n : ℝ)⁻¹ * hH.eigenvalues i = n :=
        le_antisymm harith_le (hgeom.symm.trans_le (Real.geom_mean_le_arith_mean_weighted
          Finset.univ (fun _ => (n : ℝ)⁻¹) hH.eigenvalues (fun _ _ => inv_nonneg.mpr hn'.le)
          (by simp [mul_inv_cancel₀ hn'.ne']) (fun j _ => he_nonneg j)))
      have he_eq : ∀ i, hH.eigenvalues i = n := fun i =>
        ((Real.geom_mean_eq_arith_mean_weighted_iff_of_pos' Finset.univ (fun _ => (n : ℝ)⁻¹)
          hH.eigenvalues (fun _ _ => inv_pos.mpr hn') (by simp [mul_inv_cancel₀ hn'.ne'])
          (fun j _ => he_nonneg j)).mp (hgeom.trans harith.symm) i (Finset.mem_univ i)).trans harith
      have hspec := hH.spectral_theorem
      rw [show RCLike.ofReal ∘ hH.eigenvalues = fun _ => (n : ℝ) from funext he_eq,
        hdiag_n, map_natCast] at hspec
      have hMM : M.transpose * M = ↑n := by simpa using hspec
      refine ⟨fun k j => ?_, hMM⟩
      have hdiag_j : ∑ i : Fin n, M i j * M i j = ∑ _i : Fin n, (1 : ℝ) := by
        simpa [Matrix.mul_apply, ← hdiag_n] using congrFun (congrFun hMM j) j
      have hkj :=
        (Finset.sum_eq_sum_iff_of_le (fun i _ => hsq i j)).mp hdiag_j k (Finset.mem_univ k)
      rcases mul_self_eq_one_iff.mp hkj with h1 | h1 <;> simp [h1]

/--
Both definitions are equivalent.
-/
@[category test, AMS 15]
theorem isHadamard_equiv_isHadamard' (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    IsHadamard' M ↔ IsHadamard M :=
  ⟨fun h => ⟨h.1, ((isHadamard'_iff_abs_le_one_and_det_eq n M).mp h).2⟩, fun ⟨hM, hdet⟩ =>
    (isHadamard'_iff_abs_le_one_and_det_eq n M).mpr
      ⟨fun i j => by rcases Finset.mem_insert.mp (hM i j) with h | h <;> simp_all, hdet⟩⟩

/- Note: the conjecture was originally formulated by
Hadamard as a question: "For which values of $n=4k$ does
a Hadamard matrix exist." However the expectation seems
to be that all such matrices are Hadamard, and the
formalisation has been written with this in mind. -/

/--
There exists a Hadamard matrix for all $n = 4k$.
-/
@[category research open, AMS 15]
theorem HadamardConjecture (k : ℕ) : ∃ M, IsHadamard (n := 4 * k) M := by
  sorry

/--
The **smallest unsolved order** of the Hadamard conjecture: the smallest $n = 4k$ such that there
is no Hadamard matrix of order $n$, or $\infty$ if there is none.
-/
@[optimization_constant "23a"]
noncomputable def hadamardConstant : ℕ∞ :=
  ⨅ (k : ℕ) (_ : ¬ ∃ M, IsHadamard (n := 4 * k) M), (4 * k : ℕ∞)

@[category test, AMS 15]
theorem exists_hadamard_zero : ∃ M, IsHadamard (n := 0) M := by
  use 0
  simp [IsHadamard]

/--
Hadamard constructs a 12 x 12 matrix ...
-/
def H12 : Matrix (Fin 12) (Fin 12) ℝ :=
!![  1,  1,  1,   1,  1,  1,   1,  1,  1,   1,  1,  1;
     1,  1,  1,  -1, -1, -1,  -1, -1, -1,   1,  1,  1;
     1,  1,  1,  -1, -1, -1,   1,  1,  1,  -1, -1, -1;
     1, -1, -1,   1, -1, -1,  -1,  1,  1,  -1,  1,  1;
     1, -1, -1,  -1,  1, -1,   1, -1,  1,   1, -1,  1;
     1, -1, -1,  -1, -1,  1,   1,  1, -1,   1,  1, -1;
     1, -1,  1,  -1,  1,  1,  -1,  1, -1,  -1, -1,  1;
     1, -1,  1,   1, -1,  1,  -1, -1,  1,   1, -1, -1;
     1, -1,  1,   1,  1, -1,   1, -1, -1,  -1,  1, -1;
     1,  1, -1,  -1,  1,  1,  -1, -1,  1,  -1,  1, -1;
     1,  1, -1,   1, -1,  1,   1, -1, -1,  -1, -1,  1;
     1,  1, -1,   1,  1, -1,  -1,  1, -1,   1, -1, -1 ]
/--
which satisfies the condition.
-/
@[category test, AMS 15]
theorem isHadamard_H12 : IsHadamard H12 := by
  have h : H12.transpose * H12 = (12 : ℝ) • 1 := by
    rw [← Matrix.ext_iff]
    norm_num +decide [Fin.forall_fin_succ, Matrix.mul_apply, Fin.sum_univ_succ, H12,
      Matrix.one_apply]
  have hd : H12.det ^ 2 = 12 ^ 12 := by simpa [Matrix.det_smul, ← sq] using congrArg Matrix.det h
  refine ⟨by simp [Fin.forall_fin_succ, H12], ?_⟩
  rw [← Real.sqrt_sq_eq_abs, hd]
  norm_num

/--
For all $k ≤ 166$, it is known there that there is a Hadamard matrix of size $4 * k$.
So `hadamardConstant` is at least $668$.
-/
@[category research solved, AMS 15]
theorem HadamardConjecture.variants.first_cases : 668 ≤ hadamardConstant := by
  sorry

/--
The smallest order for which no Hadamard matrix is presently known is $668 = 4 * 167$.
Is `hadamardConstant` larger than $668$?
-/
@[category research open, AMS 15]
theorem HadamardConjecture.variants.«167» : 668 < hadamardConstant := by
  sorry

end Hadamard
