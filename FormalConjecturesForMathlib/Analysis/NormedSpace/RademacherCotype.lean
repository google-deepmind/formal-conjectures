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

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Fintype.Pi

/-!
# Finite-cube Rademacher cotype and K-convexity

Uniform averages on Boolean cubes define the Rademacher projection and cotype.
The approximation property uses finite-rank continuous maps without a common
operator-norm bound.

Definitions adapted from OpenAI's
[Cotype](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Cotype.lean),
Apache-2.0. Namespace, names, and imports were changed.
-/

@[expose] public section

namespace RademacherCotype

def sign (b : Bool) : ℝ := if b then -1 else 1

noncomputable def average {ι E : Type*} [Fintype ι] [AddCommMonoid E] [Module ℝ E]
    (f : ι → E) : E := (Fintype.card ι : ℝ)⁻¹ • ∑ i, f i

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def cubeL2 {n : ℕ} (f : (Fin n → Bool) → E) : ℝ :=
  Real.sqrt (average (fun ε => ‖f ε‖ ^ 2))

def rademacherSum {n : ℕ} (x : Fin n → E) (ε : Fin n → Bool) : E :=
  ∑ i, sign (ε i) • x i

noncomputable def moment {n : ℕ} (f : (Fin n → Bool) → E) (i : Fin n) : E :=
  average (fun ε => sign (ε i) • f ε)

noncomputable def radProjection {n : ℕ} (f : (Fin n → Bool) → E) : (Fin n → Bool) → E :=
  rademacherSum E (moment E f)

/-- Uniform boundedness of the Rademacher projections on finite-cube $L^2$. -/
def KConvex : Prop := ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (f : (Fin n → Bool) → E),
  cubeL2 E (radProjection E f) ≤ K * cubeL2 E f

/-- Rademacher cotype with a finite real exponent $q \geq 2$. -/
def HasCotype (q : ℝ) : Prop := 2 ≤ q ∧ ∃ C : ℝ, 0 ≤ C ∧
  ∀ (n : ℕ) (x : Fin n → E),
    (∑ i, ‖x i‖ ^ q) ^ (1 / q) ≤ C * cubeL2 E (rademacherSum E x)

def FiniteCotype : Prop := ∃ q : ℝ, HasCotype E q

/-- Uniform approximation on each compact set by a finite-rank continuous linear map. -/
def ApproximationProperty : Prop := ∀ M : Set E, IsCompact M →
  ∀ δ : ℝ, 0 < δ → ∃ S : E →L[ℝ] E,
    FiniteDimensional ℝ (LinearMap.range S.toLinearMap) ∧ ∀ x ∈ M, ‖S x - x‖ < δ

omit [NormedSpace ℝ E] in
theorem cubeL2_nonneg {n : ℕ} (f : (Fin n → Bool) → E) : 0 ≤ cubeL2 E f :=
  Real.sqrt_nonneg _

theorem rademacherSum_zero {n : ℕ} (ε : Fin n → Bool) :
    rademacherSum E (fun _ => 0) ε = 0 := by
  simp [rademacherSum]

end RademacherCotype
