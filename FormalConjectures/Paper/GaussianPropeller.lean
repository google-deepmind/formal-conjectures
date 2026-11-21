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

public import FormalConjecturesUtil

/-!
# The Gaussian propeller bound

*Reference:* OpenAI, *The Gaussian Propeller Bound in Every Dimension* (2026),
Theorem 1.1.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Gaussian-Propeller-Bound-in-Every-Dimension-September-24-2026/main.pdf
-/

@[expose] public section

namespace GaussianPropeller

open MeasureTheory ProbabilityTheory

/-- For any measurable labelled partition of standard Gaussian space, the sum of
squared first moments is at most $9/(8\pi)$. Empty cells and arbitrary masses are
allowed. -/
@[category research solved, AMS 52 60]
theorem gaussian_partition_bound (d k : ℕ) (hd : 0 < d) (hk : 0 < k)
    (A : Fin k → Set (EuclideanSpace ℝ (Fin d)))
    (hmeas : ∀ i, MeasurableSet (A i))
    (hpartition : ∀ᵐ x ∂stdGaussian (EuclideanSpace ℝ (Fin d)), ∃! i, x ∈ A i) :
    (∑ i, ‖∫ x in A i, x ∂stdGaussian (EuclideanSpace ℝ (Fin d))‖ ^ 2) ≤
      9 / (8 * Real.pi) := by
  sorry

end GaussianPropeller
