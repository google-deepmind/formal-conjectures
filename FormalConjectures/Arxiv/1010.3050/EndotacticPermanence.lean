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
# Endotactic permanence

The Extended Permanence Conjecture asks whether all endotactic κ-variable
mass-action systems are permanent [CNP11, Section 4]. Permanence means that
all positive trajectories in each stoichiometric class eventually have common
positive lower and upper concentration bounds. A strengthening requires common
bounds for all bounded measurable rates in a fixed positive coefficient box.

References:
- [CNP11] G. Craciun, F. Nazarov and C. Pantea,
  *Persistence and permanence of mass-action and power-law dynamical systems*,
  [arXiv:1010.3050v2](https://arxiv.org/abs/1010.3050v2), Section 4.
- [Ki26] Kenta Kitamura, *Endotactic permanence*, Lean 4 formalization (2026).
  [Proof repository](https://github.com/KitaKen1/endotactic-permanence-lean/tree/bfc411af63d0b11b2fd35d6a234249fc56080205).
-/

@[expose] public section

namespace Endotactic

/-- A directed reaction network. -/
structure Network (d m : ℕ) where
  /-- The source complex of each reaction. -/
  source : Fin m → Fin d → ℕ
  /-- The target complex of each reaction. -/
  target : Fin m → Fin d → ℕ

/-- The real reaction vector: target minus source. -/
def Network.vector {d m : ℕ} (N : Network d m) (e : Fin m) : Fin d → ℝ :=
  fun i => (N.target e i : ℝ) - (N.source e i : ℝ)

/-- Each negative projected reaction has a positive projected reaction
at a strictly lower source level. -/
def Network.IsEndotactic {d m : ℕ} (N : Network d m) : Prop :=
  ∀ (r : Fin d → ℝ) (e : Fin m), dotProduct r (N.vector e) < 0 →
    ∃ f : Fin m, 0 < dotProduct r (N.vector f) ∧
      dotProduct r (fun i => (N.source f i : ℝ)) < dotProduct r (fun i => (N.source e i : ℝ))

/-- All concentrations are strictly positive. -/
def Positive {d : ℕ} (x : Fin d → ℝ) : Prop := ∀ i, 0 < x i

/-- The positive affine stoichiometric class through `c`. -/
def Network.positiveClass {d m : ℕ} (N : Network d m)
    (c : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x | Positive x ∧ x - c ∈ Submodule.span ℝ (Set.range N.vector)}

/-- The mass-action vector field. -/
def Network.rhs {d m : ℕ} (N : Network d m)
    (k : Fin m → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  ∑ e, (k e * ∏ i, x i ^ N.source e i) • N.vector e

open MeasureTheory Set

variable {d m : ℕ}

/-- Measurable rates in `[ℓ, u]` for nonnegative time. -/
def AdmissibleRates (k : Fin m → ℝ → ℝ) (ℓ u : ℝ) : Prop :=
  (∀ e, Measurable (k e)) ∧ ∀ e t, 0 ≤ t → ℓ ≤ k e t ∧ k e t ≤ u

/-- Rates differentiable off a finite set on each bounded positive time interval. -/
def LocallyPiecewiseDifferentiableRates (k : Fin m → ℝ → ℝ) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ cuts : Finset ℝ,
    ∀ e t, t ∈ Ioo 0 T → t ∉ cuts → DifferentiableAt ℝ (k e) t

/-- A global positive integral solution on nonnegative time. -/
def Network.IsGlobalPositiveSolution (N : Network d m) (k : Fin m → ℝ → ℝ)
    (x₀ : Fin d → ℝ) (x : ℝ → Fin d → ℝ) : Prop :=
  (ContinuousOn x (Ici 0) ∧ x 0 = x₀ ∧
    (∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun t => N.rhs (fun e => k e t) (x t))
      volume 0 T) ∧
    ∀ t : ℝ, 0 ≤ t →
      x t = x₀ + ∫ s in (0 : ℝ)..t, N.rhs (fun e => k e s) (x s)) ∧
    ∀ t : ℝ, 0 ≤ t → Positive (x t)

/-- A unique global positive solution on nonnegative time. -/
def Network.PositiveWellPosed (N : Network d m) (k : Fin m → ℝ → ℝ)
    (x₀ : Fin d → ℝ) : Prop :=
  ∃ x : ℝ → Fin d → ℝ, N.IsGlobalPositiveSolution k x₀ x ∧
    ∀ y : ℝ → Fin d → ℝ, N.IsGlobalPositiveSolution k x₀ y →
      ∀ t : ℝ, 0 ≤ t → y t = x t

/-- Common eventual positive coordinate bounds for all admissible rate paths. -/
def Network.UniformPermanent (N : Network d m) (ℓ u : ℝ) (c : Fin d → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    ∀ k : Fin m → ℝ → ℝ, AdmissibleRates k ℓ u →
      (∀ x₀ ∈ N.positiveClass c, N.PositiveWellPosed k x₀) ∧
      ∀ x₀ ∈ N.positiveClass c, ∀ x : ℝ → Fin d → ℝ,
        N.IsGlobalPositiveSolution k x₀ x →
          ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
            ∀ i, ε ≤ x t i ∧ x t i ≤ ε⁻¹

/-- Eventual positive coordinate bounds for one fixed rate path. -/
def Network.PermanentForRates (N : Network d m) (k : Fin m → ℝ → ℝ) (c : Fin d → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    (∀ x₀ ∈ N.positiveClass c, N.PositiveWellPosed k x₀) ∧
    ∀ x₀ ∈ N.positiveClass c, ∀ x : ℝ → Fin d → ℝ,
      N.IsGlobalPositiveSolution k x₀ x →
        ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
          ∀ i, ε ≤ x t i ∧ x t i ≤ ε⁻¹

/-- Permanence for endotactic κ-variable mass-action systems [CNP11, Section 4].
The answer is yes [Ki26]. -/
@[category research solved, AMS 34 92,
    formal_proof using lean4 at "https://github.com/KitaKen1/endotactic-permanence-lean/blob/bfc411af63d0b11b2fd35d6a234249fc56080205/lean/EndotacticPublication/FCPresentation.lean#L133"]
theorem extended_permanence :
    answer(True) ↔
      ∀ (d m : ℕ), 0 < d → ∀ N : Network d m,
        N.IsEndotactic → ∀ (ℓ u : ℝ), 0 < ℓ → ℓ ≤ u →
          ∀ k : Fin m → ℝ → ℝ, AdmissibleRates k ℓ u →
            LocallyPiecewiseDifferentiableRates k →
              ∀ c : Fin d → ℝ, Positive c →
                N.PermanentForRates k c := by
  sorry

/-- Common-box permanence for bounded measurable rates.
The answer is yes [Ki26]. -/
@[category research solved, AMS 34 92,
    formal_proof using lean4 at "https://github.com/KitaKen1/endotactic-permanence-lean/blob/bfc411af63d0b11b2fd35d6a234249fc56080205/lean/EndotacticPublication/FCPresentation.lean#L151"]
theorem measurable_extended_permanence :
    answer(True) ↔
      ∀ (d m : ℕ), 0 < d → ∀ N : Network d m,
        N.IsEndotactic → ∀ (ℓ u : ℝ), 0 < ℓ → ℓ ≤ u →
          ∀ c : Fin d → ℝ, Positive c →
            N.UniformPermanent ℓ u c := by
  sorry

end Endotactic
