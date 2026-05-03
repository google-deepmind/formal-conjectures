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
# Brennan's Conjecture

*Reference:*
- [Wikipedia](https://en.wikipedia.org/wiki/Brennan_conjecture)
- [arXiv:2409.15074](https://arxiv.org/abs/2409.15074)
- [arXiv:2512.09330](https://arxiv.org/abs/2512.09330)
-/

namespace BrennanConjecture

open Complex Filter MeasureTheory Set Topology

def unitDisk : Set ℂ := {z | ‖z‖ < 1}

/-- The standard class $\mathcal{S}$ of normalised univalent functions on $\mathbb{D}$. -/
structure IsUnivalentNormalized (f : ℂ → ℂ) : Prop where
  analyticOn : AnalyticOn ℂ f unitDisk
  injOn      : InjOn f unitDisk
  map_zero   : f 0 = 0
  deriv_zero : deriv f 0 = 1

/-- $\beta_f(\tau) := \limsup_{r \to 1^-}
\frac{\log \int_{-\pi}^{\pi} |f'(re^{i\theta})|^\tau \, d\theta}{|\log(1-r)|}$ -/
noncomputable def integralMeansSpectrum (f : ℂ → ℂ) (τ : ℝ) : ℝ :=
  limsup
    (fun r => Real.log (∫ θ in Ioc (-Real.pi) Real.pi,
        ‖deriv f (r • exp (Complex.I * θ))‖ ^ τ) /
      |Real.log (1 - r)|)
    (𝓝[Iio 1] (1 : ℝ))

noncomputable def universalSpectrum (τ : ℝ) : ℝ :=
  sSup {β | ∃ f : ℂ → ℂ, IsUnivalentNormalized f ∧ β = integralMeansSpectrum f τ}

noncomputable def universalSpectrumBounded (τ : ℝ) : ℝ :=
  sSup {β | ∃ f : ℂ → ℂ, IsUnivalentNormalized f ∧
    Bornology.IsBounded (f '' unitDisk) ∧ β = integralMeansSpectrum f τ}

@[category API, AMS 30]
theorem universalSpectrumBounded_le (τ : ℝ) :
    universalSpectrumBounded τ ≤ universalSpectrum τ := by
  apply csSup_le_csSup
  · sorry
  · sorry
  · rintro β ⟨f, hf, _, rfl⟩; exact ⟨f, hf, rfl⟩

@[category test, AMS 30]
theorem integralMeansSpectrum_id (τ : ℝ) : integralMeansSpectrum id τ = 0 := by
  sorry

/-- Brennan's conjecture, part 1: $B(-2) = 1$. -/
@[category research open, AMS 30]
theorem brennan_universalSpectrum :
    universalSpectrum (-2) = 1 := by
  sorry

/-- Brennan's conjecture, part 2: $B_b(-2) = 1$. -/
@[category research open, AMS 30]
theorem brennan_universalSpectrumBounded :
    universalSpectrumBounded (-2) = 1 := by
  sorry

/-- Brennan's conjecture, part 3: $B(-2) = B_b(-2)$. -/
@[category API, AMS 30]
theorem brennan_spectra_eq :
    universalSpectrum (-2) = universalSpectrumBounded (-2) := by
  rw [brennan_universalSpectrum, brennan_universalSpectrumBounded]

/-- Brennan's conjecture: $B(-2) = B_b(-2) = 1$. -/
@[category API, AMS 30]
theorem brennan :
    universalSpectrum (-2) = 1 ∧ universalSpectrumBounded (-2) = 1 :=
  ⟨brennan_universalSpectrum, brennan_universalSpectrumBounded⟩

end BrennanConjecture
