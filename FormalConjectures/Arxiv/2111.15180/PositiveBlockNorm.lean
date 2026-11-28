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
# Bourin and Lee's positive block-matrix conjecture

* J.-C. Bourin and E.-Y. Lee, *Eigenvalue inequalities for positive block matrices with the
  inradius of the numerical range*, [Conjecture 3.3](https://arxiv.org/html/2111.15180#S3).
* M. J. Colbrook, [Theorem 1.1](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/20861716f61359d2cf24c5d34a22d612eb3108ab/matrix-inequalities-and-norms/MI-04/solution.pdf).
  G. Stepaniants formalized the original implication in Lean.
* M. Sababheh, *An Extremal Formula for Elliptical Width and the Bourin–Lee Conjecture*,
  [arXiv:2610.04377](https://arxiv.org/abs/2610.04377).
-/

@[expose] public section

namespace Arxiv.«2111.15180»

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

variable {n : ℕ}

local notation "M" => Matrix (Fin n) (Fin n) ℂ
local notation "V" => EuclideanSpace ℂ (Fin n)
local notation "toOp" => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)

/-- An essentially Hermitian matrix is a complex affine function of a Hermitian matrix. -/
def IsEssentiallyHermitian (X : M) : Prop :=
  ∃ K : M, K.IsHermitian ∧ ∃ α β : ℂ, X = α • K + β • 1

set_option linter.style.formal_proof_palomar false in
/-- Bourin and Lee's Conjecture 3.3. If every positive semidefinite block completion of $X$
has operator norm at most $\|A+B\|$, where $A,B$ are its diagonal blocks, then $X$ is
essentially Hermitian. -/
@[category research solved, AMS 15 47, formal_proof using lean4 at
  "https://github.com/sgstepaniants/OpenProblemsInNLA/blob/63340ef17139606dce03c4d9000288129b773157/matrix-inequalities-and-norms/MI-04/lean/NLA/MI04/Conclusion.lean#L62-L70"]
theorem positive_block_norm (hn : 0 < n) (X : M)
    (hX : ∀ A B : M, (Matrix.fromBlocks A X X.conjTranspose B).PosSemidef →
      ‖Matrix.fromBlocks A X X.conjTranspose B‖ ≤ ‖A + B‖) :
    IsEssentiallyHermitian X := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- Colbrook's orthonormal-pair criterion. Equality of the off-diagonal coefficient
magnitudes on every orthonormal pair forces $X$ to be essentially Hermitian. -/
@[category research solved, AMS 15 47, formal_proof using lean4 at
  "https://github.com/sgstepaniants/OpenProblemsInNLA/blob/63340ef17139606dce03c4d9000288129b773157/matrix-inequalities-and-norms/MI-04/lean/NLA/MI04/Conclusion.lean#L22-L59"]
theorem positive_block_norm.variants.of_orthonormal_pairs (hn : 0 < n) (X : M)
    (hX : ∀ u v : V, ‖u‖ = 1 → ‖v‖ = 1 → ⟪u, v⟫_ℂ = 0 →
      ‖⟪u, toOp X v⟫_ℂ‖ = ‖⟪v, toOp X u⟫_ℂ‖) :
    IsEssentiallyHermitian X := by
  sorry

/-- An essentially Hermitian matrix has equal off-diagonal coefficient magnitudes on every
orthogonal pair. The vectors may have arbitrary lengths. -/
@[category API, AMS 15 47]
theorem IsEssentiallyHermitian.norm_inner_eq {X : M} (hX : IsEssentiallyHermitian X)
    (u v : V) (huv : ⟪u, v⟫_ℂ = 0) :
    ‖⟪u, toOp X v⟫_ℂ‖ = ‖⟪v, toOp X u⟫_ℂ‖ := by
  obtain ⟨K, hK, α, β, rfl⟩ := hX
  have hvu := inner_eq_zero_symm.mp huv
  have hsym := (hK.isSelfAdjoint.map toOp).isSymmetric u v
  simp only [map_add, map_smul, map_one, add_apply, smul_apply, one_apply_eq_self,
    inner_add_right, inner_smul_right, huv, hvu, mul_zero, add_zero, norm_mul]
  congr 1
  calc
    ‖⟪u, toOp K v⟫_ℂ‖ = ‖⟪toOp K u, v⟫_ℂ‖ := congrArg norm hsym.symm
    _ = _ := norm_inner_symm _ _

end Arxiv.«2111.15180»
