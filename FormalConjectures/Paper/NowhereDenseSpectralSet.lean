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
# Nowhere dense spectral sets

This file formalizes Problem 7.1 from Kolountzakis, Lev, and Matolcsi. The answer is
known to be negative in dimension one and is open in every dimension at least two.

*References:*
* [KLM2023] Mihail N. Kolountzakis, Nir Lev, and Máté Matolcsi,
  "Spectral sets and weak tiling." https://arxiv.org/abs/2209.04540
-/

open MeasureTheory

namespace NowhereDenseSpectralSet

/-- Problem 7.1 in [KLM2023]: can a bounded, measurable, nowhere dense set of positive
measure be spectral in dimension `d ≥ 2`? -/
@[category research open, AMS 42 46]
theorem exists_nowhereDense_spectralSet :
    answer(sorry) ↔ ∀ᵉ (d : ℕ) (hd : 2 ≤ d),
      ∃ Ω : Set (Fin d → ℝ), Bornology.IsBounded Ω ∧ MeasurableSet Ω ∧
        IsNowhereDense Ω ∧ 0 < volume Ω ∧ isSpectral Ω := by
  sorry

end NowhereDenseSpectralSet
