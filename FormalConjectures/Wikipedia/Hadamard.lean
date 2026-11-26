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

/--
Both definitions are equivalent.
-/
@[category test, AMS 15]
theorem isHadamard_equiv_isHadamard' (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    IsHadamard' M ↔ IsHadamard M := by
  simp only [IsHadamard, IsHadamard']
  have hdiag_n : Matrix.diagonal (fun _ => (n : ℝ)) = (n : Matrix (Fin n) (Fin n) ℝ) := rfl
  refine and_congr_right fun hM => ⟨fun h => ?_, fun h => ?_⟩
  · have hdet : M.det ^ 2 = (n : ℝ) ^ n := by
      simpa [Matrix.det_mul, Matrix.det_transpose, ← hdiag_n, sq] using congrArg Matrix.det h
    rw [← Real.sqrt_sq_eq_abs, hdet, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (Nat.cast_nonneg n), mul_one_div]
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Subsingleton.elim _ _
    · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have hH := Matrix.isHermitian_conjTranspose_mul_self M
      have he_nonneg := Matrix.eigenvalues_conjTranspose_mul_self_nonneg M
      have hsq : ∀ k i : Fin n, M k i * M k i = 1 := fun k i => by
        rcases Finset.mem_insert.mp (hM k i) with hk | hk <;> simp_all
      have htrace : ∑ i, hH.eigenvalues i = (n : ℝ) * n := by
        simpa [Matrix.trace, Matrix.mul_apply, hsq] using hH.trace_eq_sum_eigenvalues.symm
      have hprod : ∏ i, hH.eigenvalues i = (n : ℝ) ^ n := by
        have hdp := hH.det_eq_prod_eigenvalues.symm
        rw [Matrix.det_mul, Matrix.det_conjTranspose, star_trivial, ← sq, ← sq_abs, h,
          ← Real.rpow_natCast, ← Real.rpow_mul hn'.le,
          show (n : ℝ) / 2 * (2 : ℕ) = (n : ℝ) by norm_num, Real.rpow_natCast] at hdp
        simpa using hdp
      have harith : ∑ i : Fin n, (n : ℝ)⁻¹ * hH.eigenvalues i = n := by
        rw [← Finset.mul_sum, htrace, inv_mul_cancel_left₀ hn'.ne']
      have hgeom : ∏ i : Fin n, hH.eigenvalues i ^ (n : ℝ)⁻¹ = n := by
        rw [Real.finsetProd_rpow _ _ (fun i _ => he_nonneg i), hprod, ← Real.rpow_natCast,
          ← Real.rpow_mul hn'.le, mul_inv_cancel₀ hn'.ne', Real.rpow_one]
      have he_eq : ∀ i, hH.eigenvalues i = n := fun i =>
        ((Real.geom_mean_eq_arith_mean_weighted_iff_of_pos' Finset.univ (fun _ => (n : ℝ)⁻¹)
          hH.eigenvalues (fun _ _ => inv_pos.mpr hn') (by simp [mul_inv_cancel₀ hn'.ne'])
          (fun j _ => he_nonneg j)).mp (hgeom.trans harith.symm) i (Finset.mem_univ i)).trans harith
      have hspec := hH.spectral_theorem
      rw [show RCLike.ofReal ∘ hH.eigenvalues = fun _ => (n : ℝ) from funext he_eq,
        hdiag_n, map_natCast] at hspec
      simpa using hspec

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
