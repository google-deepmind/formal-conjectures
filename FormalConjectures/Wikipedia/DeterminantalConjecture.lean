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
# Determinantal conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Determinantal_conjecture)
-/

@[expose] public section

/- Formalisation note: Here, we represent the two normal matrices as $U_1 D_1 U_1^*$ and
$U_2 D_2 U_2^*$ respectively, where $U_1, U_2$ are unitary and $D_1, D_2$
are diagonal. This is an universal form of a normal matrix,
allowing to retrieve $\lambda (A)_i$ as ${D_1}_{i,i}$, whereas the current mathlib
doesn't support obtaining the vector of eigenvalues from a general normal
non-Hermitian matrix. -/

namespace DeterminantalConjecture

/--
Does the determinant of the sum $A + B$ of two $n \times n$ normal
complex matrices $A$ and $B$ always lie in the convex hull
of the $n!$ points $\prod\_i (\lambda(A)\_i + \lambda(B)\_{\sigma(i)})$?
Here the numbers $\lambda(A)\_i$ and $\lambda(B)\_i$ are
the eigenvalues of $A$ and $B$, and $\sigma$ is an element of the symmetric
group $S\_n$.
-/
@[category research open, AMS 15]
theorem determinantal_conjecture
    (n : Type) [Fintype n] [DecidableEq n]
    (d1 d2 : n → ℂ) (U1 U2 : unitary (Matrix n n ℂ)) :
    (U1 * Matrix.diagonal d1 * star U1 + U2 * Matrix.diagonal d2 * star U2).det
      ∈ convexHull ℝ { ∏ i, (d1 i + d2 (σ i)) | σ : Equiv.Perm n } := by
  sorry

open Matrix in
/-- For two normal $2 \times 2$ matrices the determinant lies on the segment between the
two permutation products. See [Bebiano and da Providência, §3](https://doi.org/10.3390/math13050711).
-/
@[category research solved, AMS 15]
theorem determinantal_conjecture_fin_two (a b : Fin 2 → ℂ)
    (U W : unitary (Matrix (Fin 2) (Fin 2) ℂ)) :
    (U * diagonal a * star U + W * diagonal b * star W).det ∈
      convexHull ℝ { ∏ i, (a i + b (σ i)) | σ : Equiv.Perm (Fin 2) } := by
  let V := star U * W
  let B := V.val * diagonal b * star V.val
  have hchange : (U * diagonal a * star U + W * diagonal b * star W).det =
      (diagonal a + B).det := by
    rw [← det_units_conj' (Unitary.toUnits U)]
    congr 1
    change star U.val * _ * U.val = _
    simp only [V, B, mul_add, add_mul, Submonoid.coe_mul, Unitary.coe_star, star_mul,
      star_star, ← mul_assoc, Unitary.coe_star_mul_self, one_mul]
    rw [mul_assoc, Unitary.coe_star_mul_self, mul_one]
  let p (j : Fin 2) := Complex.normSq (V.val 0 j)
  have hp : (p 0 : ℂ) + p 1 = 1 := by
    simpa [p, mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.star_def, Complex.mul_conj]
      using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M 0 0) (Unitary.coe_mul_star_self V)
  have hentry : B 0 0 = (p 0 : ℂ) * b 0 + (p 1 : ℂ) * b 1 := by
    dsimp only [B]
    rw [mul_apply, Fin.sum_univ_two]
    simp only [mul_diagonal, Matrix.star_apply, Complex.star_def, p, ← Complex.mul_conj]
    ring
  have htrace : B 0 0 + B 1 1 = b 0 + b 1 := by
    rw [← trace_fin_two]
    dsimp only [B]
    rw [trace_mul_cycle, Unitary.coe_star_mul_self,
      one_mul, trace_diagonal, Fin.sum_univ_two]
  have hdet : B.det = b 0 * b 1 := by
    dsimp only [B]
    rw [det_mul_right_comm, Unitary.mul_star_self_of_mem V.property, one_mul, det_diagonal,
      Fin.prod_univ_two]
  have hcomb : (diagonal a + B).det =
      p 0 • ((a 0 + b 0) * (a 1 + b 1)) + p 1 • ((a 0 + b 1) * (a 1 + b 0)) := by
    rw [det_fin_two] at hdet ⊢
    simp [Complex.real_smul, eq_sub_of_add_eq' htrace, hentry, eq_sub_of_add_eq' hp] at hdet ⊢
    linear_combination hdet
  rw [hchange, hcomb]
  refine convex_convexHull ℝ _ (subset_convexHull ℝ _ ?_) (subset_convexHull ℝ _ ?_)
    (Complex.normSq_nonneg _) (Complex.normSq_nonneg _) (by exact_mod_cast hp)
  · exact ⟨1, by simp [Fin.prod_univ_two]⟩
  · exact ⟨Equiv.swap 0 1, by simp [Fin.prod_univ_two]⟩

end DeterminantalConjecture
