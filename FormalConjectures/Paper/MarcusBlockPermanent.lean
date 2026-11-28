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

public import FormalConjecturesUtil

/-!
# Marcus's block permanent conjecture

Partition a Hermitian positive semidefinite matrix $A$ into $m$ block rows and columns,
with each block of order $k$. Marcus conjectured that replacing each block by its permanent
can only decrease the permanent. Tubbenhauer's Theorem 1A.1 gives the inequality for
$m \le 4$, for $m = 5$ and $k \ge 3$, and for sufficiently large $k$ for each fixed $m$.

*References:*
* [M. Marcus and H. Minc, *Permanents*, Conjecture 9 (1965)](https://doi.org/10.1080/00029890.1965.11970575)
* [D. Tubbenhauer, *Positivity in symmetric webs and block permanents*, §1A](https://arxiv.org/html/2611.22058v1#S1.SS1)
* [Open Problems in Numerical Linear Algebra, MI-12](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/matrix-inequalities-and-norms/MI-12)
-/

@[expose] public section

open scoped ComplexOrder

namespace MarcusBlockPermanent

variable {m k : ℕ} (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ)

/-- The permanent of the matrix of block permanents is at most the permanent of $A$. -/
@[category research open, AMS 15]
theorem marcus_block_permanent (hm : 2 ≤ m) (hk : 2 ≤ k) (hA : A.PosSemidef) :
    (Matrix.of fun i j : Fin m ↦ (A.submatrix (Prod.mk i) (Prod.mk j)).permanent).permanent ≤
      A.permanent := by
  sorry

/-- For entrywise nonnegative matrices, the block permanent sums exactly those terms
of the full permanent for which each block is sent to a single block. -/
@[category textbook, AMS 15]
theorem marcus_block_permanent.variants.entrywise_nonneg (hk : 0 < k) (hA : ∀ i j, 0 ≤ A i j) :
    (Matrix.of fun i j : Fin m ↦ (A.submatrix (Prod.mk i) (Prod.mk j)).permanent).permanent ≤
      A.permanent := by
  classical
  let blocks : (Equiv.Perm (Fin m) × (Fin m → Equiv.Perm (Fin k))) ↪
      Equiv.Perm (Fin m × Fin k) :=
    { toFun := fun p ↦ (Equiv.prodCongrRight p.2).trans (p.1.prodCongr (Equiv.refl _))
      inj' := by
        intro p q h
        apply Prod.ext
        · refine Equiv.ext fun i ↦ ?_
          exact congrArg (fun σ : Equiv.Perm (Fin m × Fin k) ↦ (σ (i, ⟨0, hk⟩)).1) h
        · funext i
          refine Equiv.ext fun j ↦ ?_
          exact congrArg (fun σ : Equiv.Perm (Fin m × Fin k) ↦ (σ (i, j)).2) h }
  let weight (σ : Equiv.Perm (Fin m × Fin k)) := ∏ x, A (σ x) x
  calc
    _ = ∑ σ ∈ Finset.univ.map blocks, weight σ := by
      rw [Finset.sum_map, Fintype.sum_prod_type]
      simp only [Matrix.permanent, Matrix.of_apply, Matrix.submatrix_apply, Fintype.prod_sum,
        weight, Fintype.prod_prod_type]
      rfl
    _ ≤ A.permanent := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun σ _ _ ↦ Finset.prod_nonneg fun x _ ↦ hA (σ x) x

end MarcusBlockPermanent
