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
# The sharp triangle inequality for sums of contractions

* J.-C. Bourin and E.-Y. Lee, *Diagonal and off-diagonal blocks of positive definite
  partitioned matrices*, [Corollary 4.4 and Remark 4.5](https://arxiv.org/html/2307.02034#S4).
* M. J. Colbrook proves sharpness for every $k\ge 2$ using rank-one matrices of order two.
  [Theorem 1.1](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/20861716f61359d2cf24c5d34a22d612eb3108ab/matrix-inequalities-and-norms/MI-03/solution.pdf).
  G. Stepaniants formalized the proof in Lean.
-/

@[expose] public section

namespace Arxiv.«2307.02034»

open scoped MatrixOrder Matrix.Norms.L2Operator

/-- Nonnegative errors $c$ for which $|\sum_j A_j|\le cI+\sum_j|A_j|$ holds for every
tuple of $k$ complex matrix contractions in every positive dimension. -/
def admissibleErrors (k : ℕ) : Set ℝ :=
  {c | 0 ≤ c ∧ ∀ n : ℕ, 0 < n → ∀ A : Fin k → Matrix (Fin n) (Fin n) ℂ,
    (∀ j, ‖A j‖ ≤ 1) → CFC.abs (∑ j, A j) ≤ c • 1 + ∑ j, CFC.abs (A j)}

set_option linter.style.formal_proof_palomar false in
/-- The least dimension-independent additive error for $k\ge 2$ contractions is $k/4$.
Bourin and Lee proved the bound and its sharpness for even $k$ and conjectured sharpness
for odd $k>1$. -/
@[category research solved, AMS 15 47, formal_proof using lean4 at
  "https://github.com/sgstepaniants/OpenProblemsInNLA/blob/901ba5ffad3b57557b60c7360df67659d8b8aa21/matrix-inequalities-and-norms/MI-03/lean/Solution.lean#L64-L67"]
theorem sharp_contraction_error (k : ℕ) (hk : 2 ≤ k) :
    IsLeast (admissibleErrors k) ((k : ℝ) / 4) := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- Colbrook's two-dimensional example attains the error $k/4$ on the first coordinate
for every $k\ge 2$. -/
@[category research solved, AMS 15 47, formal_proof using lean4 at
  "https://github.com/sgstepaniants/OpenProblemsInNLA/blob/901ba5ffad3b57557b60c7360df67659d8b8aa21/matrix-inequalities-and-norms/MI-03/lean/Solution.lean#L50-L60"]
theorem sharp_contraction_error.variants.two_dimensional (k : ℕ) (hk : 2 ≤ k) :
    ∃ A : Fin k → Matrix (Fin 2) (Fin 2) ℂ, (∀ j, ‖A j‖ = 1) ∧
      CFC.abs (∑ j, A j) - ∑ j, CFC.abs (A j) =
        Matrix.diagonal ![(k : ℂ) / 4, -3 * (k : ℂ) / 4] := by
  sorry

/-- One summand needs no additive error. -/
@[category API, AMS 15]
theorem sharp_contraction_error_one : IsLeast (admissibleErrors 1) 0 := by
  refine ⟨⟨le_rfl, ?_⟩, fun _ hc ↦ hc.1⟩
  intro n hn A hA
  simp

/-- An admissible error $c$ gives the error $rc$ when all summands have operator
norm at most $r$. -/
@[category API, AMS 15 47]
theorem abs_sum_le_of_mem_admissibleErrors {k n : ℕ} (hn : 0 < n) {c : ℝ}
    (hc : c ∈ admissibleErrors k) {r : ℝ} (hr : 0 ≤ r)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (hA : ∀ j, ‖A j‖ ≤ r) :
    CFC.abs (∑ j, A j) ≤ (r * c) • 1 + ∑ j, CFC.abs (A j) := by
  rcases hr.eq_or_lt with rfl | hr
  · have hz (j) : A j = 0 := norm_le_zero_iff.mp (hA j)
    simp [hz]
  let B (j : Fin k) := r⁻¹ • A j
  have hB (j) : ‖B j‖ ≤ 1 := by
    calc
      ‖B j‖ = r⁻¹ * ‖A j‖ := by
        simp only [B, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
      _ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left (hA j) (inv_nonneg.mpr hr.le)
      _ = 1 := inv_mul_cancel₀ hr.ne'
  have hcancel (j) : r • B j = A j := smul_inv_smul₀ hr.ne' _
  have habs (X : Matrix (Fin n) (Fin n) ℂ) : r • CFC.abs X = CFC.abs (r • X) := by
    rw [CFC.abs_smul, Real.norm_of_nonneg hr.le]
  simpa only [smul_add, smul_smul, habs, Finset.smul_sum, hcancel] using
    smul_le_smul_of_nonneg_left (hc.2 n hn B hB) hr.le

end Arxiv.«2307.02034»
