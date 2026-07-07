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
# Ben Green's Open Problem 54

*References:*

- [Ben Green's Open Problem 54](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.54)
- Original formulation: M. Talagrand, *Are All Sets of Positive Measure Essentially Convex?*, in Operator Theory:
Advances and Applications, 77, 1995 Birkhäuser Verlag Basel/Switzerland.
-/

open MeasureTheory ProbabilityTheory
open scoped Pointwise ENNReal

namespace Green54

/-- The infinite-dimensional Gaussian measure γ∞ on ℝ^ℕ,
defined as the countable product of standard Gaussian measures. -/
noncomputable def gaussianMeasureInf : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

/--
Let $K \subset \mathbb{R}^n$ be a balanced compact set (that is, $\lambda K \subseteq K$ whenever
$|\lambda| \leq 1$) and suppose that the normalised Gaussian measure $\gamma_n(K) \geq 0.99$.
Does $10K$ contain a compact convex set $C$ with $\gamma_n(C) \geq 0.01$?
-/
@[category research open, AMS 46 52 60]
theorem green_54 :
    answer(sorry) ↔ ∀ K : Set (ℕ → ℝ), IsCompact K → Balanced ℝ K → (0.99 : ℝ≥0∞) ≤
    gaussianMeasureInf K → ∃ C : Set (ℕ → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ (10 : ℝ) • K ∧
    (0.01 : ℝ≥0∞) ≤ gaussianMeasureInf C := by
  sorry

/--
The same statement is known to be false for 2K instead of 10K.
-/
@[category research solved, AMS 46 52 60]
theorem green_54_known_case : ¬ (∀ K : Set (ℕ → ℝ), IsCompact K → Balanced ℝ K → (0.99 : ℝ≥0∞) ≤
    gaussianMeasureInf K → ∃ C : Set (ℕ → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ (2 : ℝ) • K ∧
    (0.01 : ℝ≥0∞) ≤ gaussianMeasureInf C) := by
  sorry

end Green54
