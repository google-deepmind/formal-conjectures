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
# Maximal real projection constants: Conjecture 2.1

*Reference:* Beata Deregowska and Barbara Lewandowska,
*Maximal Projection Constants and Extremal Vector Configurations: Some Conjectures and Examples*,
[arXiv:2608.08695v1, Conjecture 2.1](https://arxiv.org/html/2608.08695v1#S2).
-/

@[expose] public section

namespace Arxiv.«2608.08695»

open scoped ENNReal

/-- A continuous linear map to a subspace is a projection if it fixes every vector in that subspace. -/
def IsProjection {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (Y : Submodule ℝ X) (P : X →L[ℝ] Y) : Prop :=
  ∀ y : Y, P (y : X) = y

/-- The relative projection constant of a subspace is the infimum of the operator norms of continuous linear projections onto it. -/
noncomputable def RelativeProjectionConstant {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (Y : Submodule ℝ X) : ℝ≥0∞ :=
  sInf {c : ℝ≥0∞ | ∃ P : X →L[ℝ] Y, IsProjection Y P ∧ c = ENNReal.ofReal ‖P‖}

universe u

/-- The absolute projection constant of a real Banach space. -/
noncomputable def absoluteProjectionConstant (Y : Type u) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] : ℝ≥0∞ :=
  sSup {c : ℝ≥0∞ | ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace ℝ X) (_ : CompleteSpace X) (i : Y →ₗᵢ[ℝ] X), c = RelativeProjectionConstant i.toLinearMap.range}

/-- A real matrix is admissible if its rows are orthonormal. -/
def IsAdmissible (m N : ℕ) (U : Matrix (Fin m) (Fin N) ℝ) : Prop :=
  U * U.transpose = 1

/-- A weight vector is admissible if its entries are nonnegative and if their squares sum to one. -/
def IsAdmissibleWeights (N : ℕ) (t : Fin N → ℝ) : Prop :=
  (∀ i : Fin N, 0 ≤ t i) ∧ (∑ i : Fin N, (t i) ^ 2) = 1

/-- The sum of absolute inner products between columns of `U`, weighted by the products of the corresponding entries of `t`. -/
noncomputable def F (m N : ℕ) (U : Matrix (Fin m) (Fin N) ℝ) (t : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, t i * t j * |(U.transpose * U) i j|

/-- The set of values of `F` over all dimensions `N >= m`, admissible matrices, and admissible weight vectors. -/
def S (m : ℕ) : Set ℝ :=
  {x : ℝ | ∃ N : ℕ, m ≤ N ∧ ∃ U : Matrix (Fin m) (Fin N) ℝ, ∃ t : Fin N → ℝ, IsAdmissible m N U ∧ IsAdmissibleWeights N t ∧ F m N U t = x}

/-- The maximal real projection constant of all $m$-dimensional real Banach spaces. -/
noncomputable def lambdaR (m : ℕ) : ℝ≥0∞ :=
  sSup {c : ℝ≥0∞ | ∃ (Y : Type) (_ : NormedAddCommGroup Y) (_ : NormedSpace ℝ Y) (_ : CompleteSpace Y), FiniteDimensional ℝ Y ∧ Module.finrank ℝ Y = m ∧ c = absoluteProjectionConstant Y}

/-- In positive dimension, the maximal real projection constant equals the supremum of the admissible matrix values (Theorem 1.1 and the identity preceding Example 2.1). -/
@[category research solved, AMS 46]
theorem lambdaR_eq_matrix_sup (m : ℕ) (hm : 0 < m) : lambdaR m = ENNReal.ofReal (sSup (S m)) := by sorry

/-- The one-dimensional matrix objective attains value $1$ at the identity matrix. -/
@[category test, AMS 46]
theorem one_mem_S_one : (1 : ℝ) ∈ S 1 := by
  refine ⟨1, le_rfl, 1, fun _ => 1, ?_⟩
  simp [IsAdmissible, IsAdmissibleWeights, F]

/-- The maximal real projection constant in dimension 6 is $16/7$ -/
@[category research open, AMS 46]
theorem conjecture_six : lambdaR 6 = 16 / 7 := by sorry

/-- The maximal real projection constant in dimension 8 is $8/3$ -/
@[category research open, AMS 46]
theorem conjecture_eight : lambdaR 8 = 8 / 3 := by sorry

end Arxiv.«2608.08695»
