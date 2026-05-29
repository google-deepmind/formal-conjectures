/-
Copyright 2025 The Formal Conjectures Authors.

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

/-
# Degree-1 Fourier Weight Conjecture

Author: Alexey Milovanov

This file states the Degree-1 Fourier Weight Conjecture (Conjecture 5.3)
from Ryan O'Donnell's "Analysis of Boolean Functions" (2014).

*Reference:* R. O'Donnell, [Analysis of Boolean Functions](https://doi.org/10.1017/CBO9781139814782) (2014), Conjecture 5.3.

The conjecture asserts that for any Linear Threshold Function (LTF),
the Fourier weight at degree at most 1 is at least $2/\pi$.
This lower bound is asymptotically tight and is achieved by the
Majority function as $n \to \infty$.
-/

module

import FormalConjectures.Util.ProblemImports

open Finset BooleanAnalysis

namespace Books.AnalysisOfBooleanFunctions

/-- English version: "If `f : 𝔽₂ⁿ → {-1, 1}` is a linear threshold function,
then its Fourier weight at degree at most 1 is at least `2/π`." -/
@ [category research open, AMS 68 42]
theorem degree_1_weight_conjecture (n : ℕ) (f : BooleanFunction n)
    (hf_bool : IsBooleanValued f)
    (h_ltf : IsLTF f) :
    𝐖_≤ f 1 ≥ 2 / Real.pi := by
  sorry

end Books.AnalysisOfBooleanFunctions
