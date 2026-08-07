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
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.MetricSpace.Basic

/-!
# Erdős Problem 953

*References:*
- [erdosproblems.com/953](https://www.erdosproblems.com/953)
- [Ha26] A. Hart, [Erdős Problem 953](https://www.ulam.ai/research/erdos953.pdf) (2026)

Erdős asked how large a measurable subset of a plane disk can be if it contains no pair of
distinct points at integer distance.  This file records the upper-bound half of the
order-of-growth resolution: for the closed-ball extremal function `M` below, `M R` is
`O(sqrt R)`.

The matching lower bound, using Sárközy's construction, is not formalised here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Erdos953

/-- The Euclidean plane, represented as finite-dimensional real Euclidean space. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- Measurable sets with no positive integer distances between distinct points. -/
def NoPositiveIntegerDistances (A : Set Plane) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ∀ n : ℕ, 0 < n → dist x y ≠ (n : ℝ)

/-- Closed-ball version of admissible sets for the upper-bound theorem. -/
def AdmissibleSet (R : ℝ) (A : Set Plane) : Prop :=
  MeasurableSet A ∧ A ⊆ Metric.closedBall (0 : Plane) R ∧ NoPositiveIntegerDistances A

/-- Lebesgue area of a set in the plane, as a real number. -/
noncomputable def area (A : Set Plane) : ℝ :=
  (volume A).toReal

/-- Extremal area of an admissible subset of the closed radius-`R` ball. -/
noncomputable def M (R : ℝ) : ℝ :=
  sSup {a : ℝ | ∃ A : Set Plane, AdmissibleSet R A ∧ area A = a}

/--
Upper-bound half of the order-of-growth resolution of Erdős Problem 953.

This theorem is deliberately stated only as the new upper estimate for `M(R)`.  Together
with Sárközy's lower-bound construction, it gives the informal asymptotic conclusion
`M(R) = R^{1/2 + o(1)}`, but that lower-bound argument is not part of this formal proof.
-/
@[category research solved, AMS 52 28, formal_proof using lean4 at
  "https://github.com/AllenGrahamHart/FormalConjectures-Bench/blob/92c12e34d75a0300be6591d812923f2ae3f82b10/formalizations/erdos953/Erdos953Formalization/Main.lean#L82"]
theorem erdos_953_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → M R ≤ C * Real.sqrt R := by
  sorry

end Erdos953

end
