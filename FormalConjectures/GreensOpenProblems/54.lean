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

*Reference:* [Ben Green's Open Problem 54](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.54)
-/

open MeasureTheory ProbabilityTheory
open scoped Pointwise

namespace Green54

/-- The standard $n$-dimensional Gaussian measure $\gamma_n$ on $\mathbb{R}^n$, defined as the
product of $n$ independent copies of the standard Gaussian measure on $\mathbb{R}$. -/
noncomputable def gaussianMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

/--
Let $K \subset \mathbb{R}^n$ be a balanced compact set (that is, $\lambda K \subseteq K$ whenever
$|\lambda| \leq 1$) and suppose that the normalised Gaussian measure $\gamma_n(K) \geq 0.99$.
Does $10K$ contain a compact convex set $C$ with $\gamma_n(C) \geq 0.01$?
-/
@[category research open, AMS 46 52 60]
theorem green_54 :
    answer(sorry) ↔ ∀ n : ℕ, ∀ K : Set (Fin n → ℝ), IsCompact K → Balanced ℝ K → (0.99 : ℝ) ≤ gaussianMeasure n K → ∃ C : Set (Fin n → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ (10 : ℝ) • K ∧
    (0.01 : ℝ) ≤ gaussianMeasure n C := by
  sorry

end Green54
