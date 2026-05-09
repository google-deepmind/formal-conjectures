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

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
# Spectral pairs and spectral sets

A measurable set `Ω ⊂ ℝᵈ` of positive finite Lebesgue measure is called a *spectral
set* if there exists a set `Λ ⊂ ℝᵈ` such that the family of complex exponentials
$\{ e^{2\pi i \langle \lambda, \cdot \rangle } \}_{\lambda \in \Lambda}$ is an
orthogonal basis of `L²(Ω, ℂ)`. The set `Λ` is then called a *spectrum* of `Ω` and
`(Ω, Λ)` is a *spectral pair*.

This file collects the basic definitions: the exponential character `expChar`, the
predicate `IsSpectralPair`, the predicate `IsSpectralSet`, and the predicate
`IsRational` for spectra contained in `ℚᵈ`.

*References:*
- [Wikipedia: Spectral set theory](https://en.wikipedia.org/wiki/Spectral_set_theory)
-/

open MeasureTheory Complex Real

namespace SpectralSets

noncomputable section

variable {d : ℕ}

/-- The complex exponential character `x ↦ exp(2π i ⟨λ, x⟩)` on `ℝᵈ`. -/
def expChar (lam : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) → ℂ :=
  fun x => Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ lam x : ℝ) : ℂ))

/--
A pair `(Ω, Λ)` is a *spectral pair* in `ℝᵈ` when `Ω` is a measurable set of positive
finite Lebesgue measure and the family of complex exponentials
$\{ e^{2\pi i \langle \lambda, \cdot \rangle} \}_{\lambda \in \Lambda}$ is an
orthogonal basis of `L²(Ω, ℂ)`.

Orthogonality is encoded by the vanishing of the inner products
$\int_\Omega e^{2\pi i \langle \lambda, x \rangle} \overline{e^{2\pi i \langle
\mu, x \rangle}}\,dx = 0$ for distinct `λ, μ ∈ Λ`. Totality (the spanning
condition) is encoded by the property that only the zero element of `L²(Ω)` is
orthogonal to every exponential `expChar λ` with `λ ∈ Λ`.
-/
structure IsSpectralPair (Ω Λ : Set (EuclideanSpace ℝ (Fin d))) : Prop where
  measurableSet_omega : MeasurableSet Ω
  volume_omega_pos : 0 < volume Ω
  volume_omega_lt_top : volume Ω < ⊤
  /-- Pairwise orthogonality of the exponentials in `L²(Ω)`. -/
  orthogonal : Λ.Pairwise fun lam mu =>
    ∫ x in Ω, expChar lam x * star (expChar mu x) = 0
  /-- Totality: only the zero `L²(Ω)` function is orthogonal to every exponential. -/
  total : ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f 2 (volume.restrict Ω) →
    (∀ lam ∈ Λ, ∫ x in Ω, f x * star (expChar lam x) = 0) →
    f =ᵐ[volume.restrict Ω] 0

/--
`Ω ⊂ ℝᵈ` is a *spectral set* if there exists a `Λ ⊂ ℝᵈ` making `(Ω, Λ)` a spectral
pair.
-/
def IsSpectralSet (Ω : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ Λ : Set (EuclideanSpace ℝ (Fin d)), IsSpectralPair Ω Λ

/--
A subset `Λ ⊂ ℝᵈ` is *rational* if every coordinate of every element of `Λ` is a
rational number.
-/
def IsRational (Λ : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ lam ∈ Λ, ∀ i : Fin d, ∃ q : ℚ, (q : ℝ) = lam.ofLp i

end

end SpectralSets
