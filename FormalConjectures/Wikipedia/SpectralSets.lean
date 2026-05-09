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
# Spectral sets and rational spectra

A measurable set `Ω ⊂ ℝᵈ` of positive finite Lebesgue measure is called a *spectral
set* if there exists a set `Λ ⊂ ℝᵈ` such that the family of complex exponentials
$\{ e^{2\pi i \langle \lambda, \cdot \rangle } \}_{\lambda \in \Lambda}$ is an
orthogonal basis of `L²(Ω, ℂ)`. The set `Λ` is then called a *spectrum* of `Ω` and
`(Ω, Λ)` is a *spectral pair*.

This file states the conjecture: for a bounded spectral set `E ⊂ ℝ`, every spectrum
`Λ` of `E` is contained in `ℚ` (i.e., is rational). More generally, every spectral
set in `ℝᵈ` admits a spectrum contained in `ℚᵈ`.

*References:*
- [Wikipedia: Spectral set theory](https://en.wikipedia.org/wiki/Spectral_set_theory)
- [Lev, Matolcsi, *The Fuglede conjecture for convex domains is true in all
  dimensions*, Acta Math. 228 (2022), 385-420.](https://arxiv.org/abs/1904.12262)
-/

open MeasureTheory Complex Real

namespace SpectralSets

/--
**Spectral set conjecture (rationality of the spectrum).**
For every bounded spectral subset `E ⊂ ℝ`, every spectrum `Λ` of `E` is rational,
i.e. contained in `ℚ`.
-/
@[category research open, AMS 28 42 43]
theorem spectrum_is_rational :
    answer(sorry) ↔ ∀ E : Set (EuclideanSpace ℝ (Fin 1)), Bornology.IsBounded E →
      ∀ Λ : Set (EuclideanSpace ℝ (Fin 1)), IsSpectralPair E Λ → IsRational Λ := by
  sorry

end SpectralSets
