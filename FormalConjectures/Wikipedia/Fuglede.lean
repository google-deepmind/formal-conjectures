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

import FormalConjectures.Util.ProblemImports

/-!
# Fuglede's conjecture in dimensions 1 and 2

*References:*
- [Fuglede's conjecture](https://en.wikipedia.org/wiki/Fuglede%27s_conjecture)
-/

namespace Fuglede

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
noncomputable def expFunction {d : ℕ} (ξ x : Fin d → ℝ) : ℂ :=
  Complex.exp (2 * π * Complex.I * (∑ i, ξ i * x i))

/--
Exponential function as an element of L^2(Ω) which is `Lp ℂ 2 (volume.restrict Ω)`.
-/
lemma expFunction_is_L2 {d : ℕ} (Ω : Set (Fin d → ℝ)) (ξ : Fin d → ℝ) (hΩ_finite : volume Ω ≠ ⊤) :
    MemLp (expFunction ξ) 2 (volume.restrict Ω) := by
    have h_expFunction_continuous : Continuous (expFunction ξ) := by
      unfold expFunction
      continuity
    have h_expFunction_measurable : AEStronglyMeasurable (expFunction ξ) (volume.restrict Ω) := by
      exact (h_expFunction_continuous).aestronglyMeasurable
    have h_expFunction_sqnorm1 (x : Fin d → ℝ) : ‖expFunction ξ x‖^2 = 1 := by
      unfold expFunction
      have h_simp :
        2 * π * Complex.I * (∑ i, ξ i * x i) = Complex.I * ((2 * π * ∑ i, ξ i * x i) : ℝ) := by
          simp
          ring
      rw [h_simp, Complex.norm_exp_I_mul_ofReal]
      norm_num
    rw [MeasureTheory.memLp_two_iff_integrable_sq_norm h_expFunction_measurable]
    simp_rw [h_expFunction_sqnorm1]
    change IntegrableOn (fun _ ↦ (1 : ℝ)) Ω volume
    exact MeasureTheory.integrableOn_const hΩ_finite

/--
(Ω, Λ) is called a spectral pair if Λ is a spectrum for Ω, i.e.
a set Λ of frequencies such that the functions
e^(2πi ⟨ξ, x⟩) for ξ in Λ form an orthogonal basis of L^2(Ω).
-/
def spectralPair {d : ℕ} (Ω Λ : Set (Fin d → ℝ)) : Prop :=
  ∃ hΩ_finite : volume Ω ≠ ⊤,
    let e : (Fin d → ℝ) → MeasureTheory.Lp ℂ 2 (volume.restrict Ω) := fun ξ ↦
      MeasureTheory.MemLp.toLp (expFunction ξ) (expFunction_is_L2 Ω ξ hΩ_finite)
    (∀ ξ1 ∈ Λ, ∀ ξ2 ∈ Λ, ξ1 ≠ ξ2 → ⟪e ξ1, e ξ2⟫_ℂ = 0) ∧
    Submodule.topologicalClosure (Submodule.span ℂ (Set.range fun (ξ : Λ) ↦ e ξ.val)) = ⊤

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

/--
**Fuglede's conjecture** in one dimension: A bounded subset of ℝ with positive Lebesgue measure is spectral iff it tiles ℝ by translation.
-/
@[category research open, AMS 42 46 47]
theorem FugledeConjecture.variants.dim_1 :
    answer(sorry) ↔
      ∀ Ω : Set (Fin 1 → ℝ),
        Bornology.IsBounded Ω → MeasurableSet Ω → 0 < volume Ω →
          (isSpectral Ω ↔ tilesByTranslation Ω) := by
  sorry

/--
**Fuglede's conjecture** in two dimensions: A bounded subset of ℝ^2 with positive Lebesgue measure is spectral iff it tiles ℝ^2 by translation.
-/
@[category research open, AMS 42 46 47]
theorem FugledeConjecture.variants.dim_2 :
    answer(sorry) ↔
      ∀ Ω : Set (Fin 2 → ℝ),
        Bornology.IsBounded Ω → MeasurableSet Ω → 0 < volume Ω →
          (isSpectral Ω ↔ tilesByTranslation Ω) := by
  sorry

end Fuglede
