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

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.LinearAlgebra.Matrix.Permanent

/-!
# Generalized matrix functions

A generalized matrix function weights each permutation product by a function on a subgroup
of the symmetric group. The constant weight one on the full group gives the permanent.
-/

@[expose] public section

namespace Matrix

variable {ι R : Type*} [DecidableEq ι] [Fintype ι] [CommSemiring R] {G : Subgroup (Equiv.Perm ι)}

open scoped Classical in
/-- The generalized matrix function with weight $w$ on a group of permutations of the indices. -/
noncomputable def generalizedMatrixFunction (A : Matrix ι ι R) (w : G → R) : R :=
  ∑ σ : G, w σ * ∏ i, A i (σ.1 i)

/-- On a diagonal matrix only the identity permutation contributes. -/
theorem generalizedMatrixFunction_diagonal (d : ι → R) (w : G → R) :
    (diagonal d).generalizedMatrixFunction w = w 1 * ∏ i, d i := by
  classical
  unfold generalizedMatrixFunction
  rw [Finset.sum_eq_single (1 : G)]
  · simp
  · intro σ _ hσ
    obtain ⟨i, hi⟩ : ∃ i, i ≠ σ.1 i := by
      by_contra! h
      exact hσ (Subtype.ext (Equiv.ext fun i ↦ (h i).symm))
    apply mul_eq_zero_of_right
    exact Finset.prod_eq_zero (Finset.mem_univ i) (diagonal_apply_ne d hi)
  · simp

/-- Constant weight one on the full permutation group recovers the permanent. -/
theorem generalizedMatrixFunction_top_one (A : Matrix ι ι R) :
    A.generalizedMatrixFunction (fun _ : (⊤ : Subgroup (Equiv.Perm ι)) ↦ 1) = A.permanent := by
  classical
  rw [← permanent_transpose A]
  simpa [generalizedMatrixFunction, permanent] using
    (Subgroup.topEquiv (G := Equiv.Perm ι)).toEquiv.sum_comp (fun σ ↦ ∏ i, A i (σ i))

end Matrix
