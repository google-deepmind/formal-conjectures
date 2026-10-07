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

import Mathlib

/-!
# Exact rational LDLᵀ certificates (kernel-checkable)

The Lean form of `harness/sdk/exact_ldlt.py` (`verify_exact_ldlt`): a certificate is a rational
matrix `A`, a lower factor `L` and a diagonal `D` with `A = L D Lᵀ` and `D ≥ 0`.  `ldltCheck` is a
`Bool` over `ℚ`; `ldltCheck_sound` turns `ldltCheck n A L D = true` into

  `0 ≤ Re Σ_{i,j} conj(z_i) z_j A_{ij} = Σ_k D_k |Σ_i L_{ik} z_i|²`   for every complex `z`,

so a closed instance is discharged by `decide +kernel`.  Used for the Schur matrix of the Feshbach
certificates.  AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false

namespace AEGIS.RHExactLDLTV1

open Finset

/-- Entry `(i, j)` of a list-of-rows matrix (zero outside). -/
def ent (A : List (List ℚ)) (i j : ℕ) : ℚ := (A.getD i []).getD j 0

/-- `Σ_{k<n} L_{ik} D_k L_{jk}`. -/
def ldlEntry (n : ℕ) (L : List (List ℚ)) (D : List ℚ) (i j : ℕ) : ℚ :=
  ∑ k ∈ range n, ent L i k * D.getD k 0 * ent L j k

def ldltCheck (n : ℕ) (A L : List (List ℚ)) (D : List ℚ) : Bool :=
  (List.range n).all (fun k => decide (0 ≤ D.getD k 0)) &&
    (List.range n).all (fun i => (List.range n).all (fun j =>
      decide (ent A i j = ldlEntry n L D i j)))

theorem ldltCheck_spec (n : ℕ) (A L : List (List ℚ)) (D : List ℚ)
    (h : ldltCheck n A L D = true) :
    (∀ k < n, 0 ≤ D.getD k 0) ∧ ∀ i < n, ∀ j < n, ent A i j = ldlEntry n L D i j := by
  simp only [ldltCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact ⟨fun k hk => h.1 k hk, fun i hi j hj => h.2 i hi j hj⟩

/-- The Hermitian form of `A` at `z`. -/
noncomputable def herm (n : ℕ) (A : List (List ℚ)) (z : ℕ → ℂ) : ℂ :=
  ∑ i ∈ range n, ∑ j ∈ range n, (starRingEnd ℂ) (z i) * z j * (ent A i j : ℂ)

theorem herm_eq_sum_sq (n : ℕ) (A L : List (List ℚ)) (D : List ℚ)
    (hA : ∀ i < n, ∀ j < n, ent A i j = ldlEntry n L D i j) (z : ℕ → ℂ) :
    herm n A z = ∑ k ∈ range n, ((D.getD k 0 : ℚ) : ℂ) *
      ((starRingEnd ℂ) (∑ i ∈ range n, (ent L i k : ℂ) * z i) *
        ∑ j ∈ range n, (ent L j k : ℂ) * z j) := by
  unfold herm
  have h1 : ∀ i ∈ range n, ∀ j ∈ range n,
      (starRingEnd ℂ) (z i) * z j * (ent A i j : ℂ) =
        ∑ k ∈ range n, ((D.getD k 0 : ℚ) : ℂ) *
          ((ent L i k : ℂ) * (starRingEnd ℂ) (z i) * ((ent L j k : ℂ) * z j)) := by
    intro i hi j hj
    rw [hA i (mem_range.mp hi) j (mem_range.mp hj), ldlEntry]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => h1 i hi j hj))]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  simp only [map_mul, Complex.conj_ofReal, map_ratCast]

theorem ldltCheck_sound (n : ℕ) (A L : List (List ℚ)) (D : List ℚ)
    (h : ldltCheck n A L D = true) (z : ℕ → ℂ) : 0 ≤ (herm n A z).re := by
  obtain ⟨hD, hA⟩ := ldltCheck_spec n A L D h
  rw [herm_eq_sum_sq n A L D hA z, Complex.re_sum]
  apply Finset.sum_nonneg
  intro k hk
  set w := ∑ i ∈ range n, (ent L i k : ℂ) * z i
  have hw : (starRingEnd ℂ) w * w = ((Complex.normSq w : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
  rw [hw, ← Complex.ofReal_ratCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hD' : (0 : ℝ) ≤ ((D.getD k 0 : ℚ) : ℝ) := by exact_mod_cast hD k (mem_range.mp hk)
  exact mul_nonneg hD' (Complex.normSq_nonneg _)

/-- A `2 × 2` sanity instance, closed by the kernel. -/
example : ldltCheck 2 [[4, 2], [2, 3]] [[1, 0], [1/2, 1]] [4, 2] = true := by decide +kernel

end AEGIS.RHExactLDLTV1

#print axioms AEGIS.RHExactLDLTV1.ldltCheck_sound
