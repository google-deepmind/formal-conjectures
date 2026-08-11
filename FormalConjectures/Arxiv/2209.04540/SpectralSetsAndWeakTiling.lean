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

import FormalConjecturesUtil

/-!
# Spectral sets and weak tiling

This file formalizes Problems 7.1 and 7.2 from Kolountzakis, Lev, and Matolcsi.

*References:*
- [KLM2023] Mihail N. Kolountzakis, Nir Lev, and Máté Matolcsi,
  [Spectral sets and weak tiling](https://arxiv.org/abs/2209.04540).
- [GL16] Rachel Greenfeld and Nir Lev, Spectrality and tiling by cylindric domains,
  *Journal of Functional Analysis* 271 (2016), 2808–2821.
- [GL20] Rachel Greenfeld and Nir Lev, Spectrality of product domains and Fuglede's conjecture
  for convex polytopes, *Journal d'Analyse Mathématique* 140 (2020), 409–441.
-/

open MeasureTheory

namespace NowhereDenseSpectralSet

/--
[KLM2023, Problem 7.1] asks whether a bounded, measurable, nowhere dense subset
$\Omega \subset \mathbb{R}^d$ of positive measure can be spectral for every $d \ge 2$.
-/
@[category research open, AMS 42 46]
theorem exists_nowhereDense_spectralSet :
    answer(sorry) ↔ ∀ᵉ (d : ℕ) (hd : 2 ≤ d),
      ∃ Ω : Set (Fin d → ℝ), Bornology.IsBounded Ω ∧ MeasurableSet Ω ∧
        IsNowhereDense Ω ∧ 0 < volume Ω ∧ isSpectral Ω := by
  sorry

end NowhereDenseSpectralSet

namespace SpectralSetProduct

/-- The product $A \times B$, represented by consecutive coordinate blocks. -/
def productSet {n m : ℕ} (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ)) :
    Set (Fin (n + m) → ℝ) :=
  {x | (fun i ↦ x (Fin.castAdd m i)) ∈ A ∧ (fun j ↦ x (Fin.natAdd n j)) ∈ B}

/-- Spectrality of a product with an `n`-dimensional convex body forces spectrality of its
bounded, measurable `m`-dimensional right factor. -/
def spectralProductImpliesRightSpectral (n m : ℕ) : Prop :=
  ∀ (A : ConvexBody (Fin n → ℝ)) (B : Set (Fin m → ℝ)),
    Bornology.IsBounded B → MeasurableSet B →
      isSpectral (productSet (A : Set (Fin n → ℝ)) B) → isSpectral B

/--
[KLM2023, Problem 7.2; GL16] For a one-dimensional convex body $A$ and a bounded,
measurable set $B$, if $A \times B$ is spectral, then $B$ is spectral.
-/
@[category research solved, AMS 42 46]
theorem isSpectral_right_of_product_one_dimensional :
    answer(True) ↔
      ∀ (m : ℕ), 0 < m → spectralProductImpliesRightSpectral 1 m := by
  sorry

/--
[KLM2023, Problem 7.2; GL20] For a two-dimensional convex body $A$ and a bounded,
measurable set $B$, if $A \times B$ is spectral, then $B$ is spectral.
-/
@[category research solved, AMS 42 46]
theorem isSpectral_right_of_product_two_dimensional :
    answer(True) ↔
      ∀ (m : ℕ), 0 < m → spectralProductImpliesRightSpectral 2 m := by
  sorry

/--
[KLM2023, Problem 7.2] For a three-dimensional convex body $A$ and a bounded,
measurable set $B$, must spectrality of $A \times B$ imply spectrality of $B$?
-/
@[category research open, AMS 42 46]
theorem isSpectral_right_of_product_three_dimensional :
    answer(sorry) ↔
      ∀ (m : ℕ), 0 < m → spectralProductImpliesRightSpectral 3 m := by
  sorry

/--
[KLM2023, Problem 7.2] For every positive dimension $n$, a convex body $A$ and a bounded,
measurable set $B$, must spectrality of $A \times B$ imply spectrality of $B$?
-/
@[category research open, AMS 42 46]
theorem isSpectral_right_of_product_of_convexBody :
    answer(sorry) ↔
      ∀ (n m : ℕ), 0 < n → 0 < m →
        spectralProductImpliesRightSpectral n m := by
  sorry

end SpectralSetProduct
