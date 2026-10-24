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

public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Projective measurements

A projective measurement on $\mathbb{C}^D$ with outcomes `Fin m` is a family of orthogonal
projections that sum to the identity. A complete von Neumann measurement is the projective
measurement in an orthonormal basis: here the basis is formed by the columns of a unitary matrix
`U`, and outcome `a` has the rank-one projection $U |a\rangle\langle a| U^{\dagger}$.

## Main definitions

- `Matrix.IsProjectiveMeasurement`: a family of orthogonal projections summing to `1`.
- `Matrix.vonNeumannMeasurement`: the complete von Neumann measurement in the basis given by the
  columns of a matrix `U`.

## Main results

- `Matrix.isProjectiveMeasurement_vonNeumannMeasurement`: for unitary `U` this is a projective
  measurement.
- `Matrix.trace_vonNeumannMeasurement`: its projections have rank one (trace `1`).
-/

@[expose] public section

namespace Matrix

/-- `P` is a projective measurement with outcomes `Fin m` on $\mathbb{C}^D$: every `P a` is an
orthogonal projection (Hermitian and idempotent), and $\sum_a P_a = 1$. -/
def IsProjectiveMeasurement {m D : ℕ} (P : Fin m → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  (∀ a, (P a).IsHermitian ∧ P a * P a = P a) ∧ ∑ a, P a = 1

/-- The complete von Neumann measurement in the orthonormal basis formed by the columns
$u_0, \dots, u_{d-1}$ of a unitary `U`: outcome `a` has the rank-one projection
$|u_a\rangle\langle u_a| = U |a\rangle\langle a| U^{\dagger}$. -/
noncomputable def vonNeumannMeasurement {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (a : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  U * single a a 1 * Uᴴ

private lemma conjTranspose_mul_self_of_mem_unitaryGroup {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ unitaryGroup (Fin d) ℂ) : Uᴴ * U = 1 := by
  have h := mem_unitaryGroup_iff'.1 hU
  rwa [star_eq_conjTranspose] at h

private lemma mul_conjTranspose_self_of_mem_unitaryGroup {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ unitaryGroup (Fin d) ℂ) : U * Uᴴ = 1 := by
  have h := mem_unitaryGroup_iff.1 hU
  rwa [star_eq_conjTranspose] at h

/-- A complete von Neumann measurement in the basis of a unitary matrix is a projective
measurement. -/
theorem isProjectiveMeasurement_vonNeumannMeasurement {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ unitaryGroup (Fin d) ℂ) : IsProjectiveMeasurement (vonNeumannMeasurement U) := by
  have h1 := conjTranspose_mul_self_of_mem_unitaryGroup hU
  have h2 := mul_conjTranspose_self_of_mem_unitaryGroup hU
  refine ⟨fun a => ⟨?_, ?_⟩, ?_⟩
  · unfold vonNeumannMeasurement
    rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      conjTranspose_single, star_one, Matrix.mul_assoc]
  · unfold vonNeumannMeasurement
    calc U * single a a 1 * Uᴴ * (U * single a a 1 * Uᴴ)
        = U * (single a a 1 * (Uᴴ * U) * single a a 1) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * single a a 1 * Uᴴ := by
          rw [h1, Matrix.mul_one, single_mul_single_same, mul_one, Matrix.mul_assoc]
  · unfold vonNeumannMeasurement
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_single_one, Matrix.mul_one, h2]

/-- The projections of a complete von Neumann measurement in the basis of a unitary matrix have
rank one (trace $1$). -/
theorem trace_vonNeumannMeasurement {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ unitaryGroup (Fin d) ℂ) (a : Fin d) : (vonNeumannMeasurement U a).trace = 1 := by
  rw [vonNeumannMeasurement, trace_mul_comm, ← Matrix.mul_assoc,
    conjTranspose_mul_self_of_mem_unitaryGroup hU, Matrix.one_mul, trace_single_eq_same]

/-- In the computational basis (`U = 1`), the von Neumann measurement is given by the matrix
units $|a\rangle\langle a|$. -/
theorem vonNeumannMeasurement_one {d : ℕ} (a : Fin d) :
    vonNeumannMeasurement 1 a = single a a 1 := by
  simp [vonNeumannMeasurement]

end Matrix
