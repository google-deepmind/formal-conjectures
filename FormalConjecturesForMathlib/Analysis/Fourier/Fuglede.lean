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

public import FormalConjecturesForMathlib.Geometry.Euclidean
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Continuity

@[expose] public section

open Real Set Complex MeasureTheory
open scoped InnerProductSpace

/--
Translate set Ω by vector t.
-/
def translatedSet {d : ℕ} (Ω: Set (Fin d → ℝ)) (t : Fin d → ℝ) :
  Set (Fin d → ℝ) :=
  {x | x - t ∈ Ω}

/--
Exponential function e^(2πi ⟨ξ, x⟩).
-/
noncomputable def exponentialCharacter {d : ℕ} (ξ x : Fin d → ℝ) : ℂ :=
  Complex.exp (2 * π * Complex.I * (∑ i, ξ i * x i))

/--
(Ω, Λ) is called a spectral pair if Λ is a spectrum for Ω, i.e.
a set Λ of frequencies such that the functions
e^(2πi ⟨ξ, x⟩) for ξ in Λ form an orthogonal basis of L^2(Ω).
-/
def spectralPair {d : ℕ} (Ω Λ : Set (Fin d → ℝ)) : Prop :=
  ∃ hΩ_finite : volume Ω ≠ ⊤,
    let hL2 : ∀ ξ : Fin d → ℝ, MemLp (exponentialCharacter ξ) 2 (volume.restrict Ω) := fun ξ => by
      have h_exponentialCharacter_continuous : Continuous (exponentialCharacter ξ) := by
        unfold exponentialCharacter
        continuity
      have h_exponentialCharacter_measurable :
          AEStronglyMeasurable (exponentialCharacter ξ) (volume.restrict Ω) := by
        exact h_exponentialCharacter_continuous.aestronglyMeasurable
      have h_exponentialCharacter_sqnorm1 (x : Fin d → ℝ) : ‖exponentialCharacter ξ x‖ ^ 2 = 1 := by
        unfold exponentialCharacter
        have h_simp :
            2 * π * Complex.I * (∑ i, ξ i * x i) =
              Complex.I * ((2 * π * ∑ i, ξ i * x i) : ℝ) := by
          simp
          ring
        rw [h_simp, Complex.norm_exp_I_mul_ofReal]
        norm_num
      rw [MeasureTheory.memLp_two_iff_integrable_sq_norm h_exponentialCharacter_measurable]
      simp_rw [h_exponentialCharacter_sqnorm1]
      change IntegrableOn (fun _ ↦ (1 : ℝ)) Ω volume
      exact MeasureTheory.integrableOn_const hΩ_finite
    let e : (Fin d → ℝ) → MeasureTheory.Lp ℂ 2 (volume.restrict Ω) := fun ξ ↦
      MeasureTheory.MemLp.toLp (exponentialCharacter ξ) (hL2 ξ)
    (∀ ξ1 ∈ Λ, ∀ ξ2 ∈ Λ, ξ1 ≠ ξ2 → ⟪e ξ1, e ξ2⟫_ℂ = 0) ∧
    Submodule.topologicalClosure (Submodule.span ℂ (Set.range fun (ξ : Λ) ↦ e ξ.1)) = ⊤

/--
`isSpectral Ω` means there exists a Λ such that (Ω, Λ) is a spectral pair.
-/
def isSpectral {d : ℕ} (Ω : Set (Fin d → ℝ)) : Prop :=
  ∃ Λ : Set (Fin d → ℝ), spectralPair Ω Λ

/--
`tilesByTranslation Ω` means there exists a set T of translation vectors
such that all of the translates of Ω by T tile ℝ^d (cover ℝ^d without overlap).
-/
def tilesByTranslation {d : ℕ} (Ω : Set (Fin d → ℝ)) : Prop :=
  ∃ T : Set (Fin d → ℝ), T.Countable ∧
    volume (Set.univ \ (⋃ t ∈ T, translatedSet Ω t)) = 0 ∧
    (∀ {t₁ t₂ : Fin d → ℝ}, t₁ ∈ T → t₂ ∈ T → t₁ ≠ t₂ →
      volume (translatedSet Ω t₁ ∩ translatedSet Ω t₂) = 0)
