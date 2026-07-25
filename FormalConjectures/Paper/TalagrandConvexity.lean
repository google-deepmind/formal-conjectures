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
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Talagrand's Convexity Problem

This file formalizes Talagrand's problem on creating convexity from a
dimension-independent number of Minkowski sums. The problem was solved
affirmatively in 2026.

*References:*
* [Talagrand] Michel Talagrand, "Create convexity in 3 (or 100?) steps only!"
  https://michel.talagrand.net/prizes/convexity.pdf
* [HST2026] Dongming Merrick Hua, Antoine Song, and Stefan Tudose,
  "On Talagrand's Convexity Conjecture." https://arxiv.org/abs/2605.10908
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Pointwise

namespace TalagrandConvexity

/-- The standard Gaussian measure on the Euclidean space `Fin n → ℝ`. -/
noncomputable def standardGaussianMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ ↦ gaussianReal 0 1

/-- The `q`-fold Minkowski sum of a set with itself. The zeroth sum is `{0}`. -/
def minkowskiNSum {E : Type*} [AddMonoid E] : ℕ → Set E → Set E
  | 0, _ => {0}
  | q + 1, A => minkowskiNSum q A + A

/-- Talagrand's convexity problem, solved affirmatively by Hua, Song, and Tudose in 2026:
there is a dimension-independent positive number of Minkowski sums such that every compact
balanced set of standard Gaussian measure at least `1 / 2` has a compact convex subset of
the resulting sum with standard Gaussian measure at least `1 / 2`. -/
@[category research solved, AMS 28 46 52]
theorem talagrandConvexityProblem :
    ∃ q : ℕ, 0 < q ∧ ∀ (n : ℕ), 0 < n → ∀ A : Set (Fin n → ℝ),
      IsCompact A → Balanced ℝ A →
        (1 / 2 : ℝ≥0∞) ≤ standardGaussianMeasure n A →
          ∃ C : Set (Fin n → ℝ), IsCompact C ∧ Convex ℝ C ∧
            C ⊆ minkowskiNSum q A ∧
              (1 / 2 : ℝ≥0∞) ≤ standardGaussianMeasure n C := by
  sorry

end TalagrandConvexity
