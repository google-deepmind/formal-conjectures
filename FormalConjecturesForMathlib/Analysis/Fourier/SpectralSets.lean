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

/-!
# Spectral sets

This file defines the basic notions used in problems related to spectral sets
and Fuglede's conjecture: translations, exponential characters,
spectral pairs, spectral sets, and translational tilings in Euclidean space.
-/

open Real Set Complex MeasureTheory
open scoped InnerProductSpace

/-- The translate of a set `Ω` by a vector `t`.-/
def translate {d : ℕ} (Ω: Set (Fin d → ℝ)) (t : Fin d → ℝ) :
  Set (Fin d → ℝ) :=
  {x | x - t ∈ Ω}

/-- The exponential character `x ↦ exp(2π i ⟪ξ, x⟫)`. -/
noncomputable def exponentialCharacter {d : ℕ} (ξ x : Fin d → ℝ) : ℂ :=
  Complex.exp (2 * π * Complex.I * (∑ i, ξ i * x i))

/--
(Ω, Λ) is called a spectral pair if Λ is a spectrum for Ω, i.e.
a set Λ of frequencies such that the associated exponential characters
 form an orthogonal basis of L^2(Ω).
-/
def spectralPair {d : ℕ} (Ω Λ : Set (Fin d → ℝ)) : Prop :=
  ∃ hΩ_finite : volume Ω ≠ ⊤,
    let hL2 : ∀ ξ : Fin d → ℝ, MemLp (exponentialCharacter ξ) 2 (volume.restrict Ω) := fun ξ => by
      have h_cont : Continuous (exponentialCharacter ξ) := by
        unfold exponentialCharacter
        continuity
      have h_meas :
          AEStronglyMeasurable (exponentialCharacter ξ) (volume.restrict Ω) := by
        exact h_cont.aestronglyMeasurable
      have h_norm (x : Fin d → ℝ) : ‖exponentialCharacter ξ x‖ ^ 2 = 1 := by
        unfold exponentialCharacter
        have h_simp :
            2 * π * Complex.I * (∑ i, ξ i * x i) =
              Complex.I * ((2 * π * ∑ i, ξ i * x i) : ℝ) := by
          simp
          ring
        rw [h_simp, Complex.norm_exp_I_mul_ofReal]
        norm_num
      rw [MeasureTheory.memLp_two_iff_integrable_sq_norm h_meas]
      simp_rw [h_norm]
      change IntegrableOn (fun _ ↦ (1 : ℝ)) Ω volume
      exact MeasureTheory.integrableOn_const hΩ_finite
    let e : (Fin d → ℝ) → MeasureTheory.Lp ℂ 2 (volume.restrict Ω) := fun ξ ↦
      MeasureTheory.MemLp.toLp (exponentialCharacter ξ) (hL2 ξ)
    (∀ ξ₁ ∈ Λ, ∀ ξ₂ ∈ Λ, ξ₁ ≠ ξ₂ → ⟪e ξ₁, e ξ₂⟫_ℂ = 0) ∧
    Submodule.topologicalClosure (Submodule.span ℂ (Set.range fun (ξ : Λ) ↦ e ξ.1)) = ⊤

/--
A set is spectral if it belongs to a spectral pair.
-/
def isSpectral {d : ℕ} (Ω : Set (Fin d → ℝ)) : Prop :=
  ∃ Λ : Set (Fin d → ℝ), spectralPair Ω Λ

/--
A set Ω tiles ℝ^d by translation if there exists a set T of translation vectors
such that the translates of Ω by T cover ℝ^d without overlap.
-/
def tilesByTranslation {d : ℕ} (Ω : Set (Fin d → ℝ)) : Prop :=
  ∃ T : Set (Fin d → ℝ), T.Countable ∧
    volume (Set.univ \ (⋃ t ∈ T, translate Ω t)) = 0 ∧
    (∀ {t₁ t₂ : Fin d → ℝ}, t₁ ∈ T → t₂ ∈ T → t₁ ≠ t₂ →
      volume (translate Ω t₁ ∩ translate Ω t₂) = 0)
