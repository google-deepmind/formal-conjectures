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
# Erdős Problem 1069

*Reference:* [erdosproblems.com/1069](https://www.erdosproblems.com/1069)
-/

open EuclideanGeometry Affine

namespace Erdos1069

/-- A line in the plane: an affine subspace whose direction is one-dimensional. -/
def IsLine (L : AffineSubspace ℝ ℝ²) : Prop :=
  Module.finrank ℝ L.direction = 1

/-- The number of $k$-rich lines determined by a finite point set `P`. -/
noncomputable def kRichLines (P : Finset ℝ²) (k : ℕ) : ℕ :=
  { L : AffineSubspace ℝ ℝ² | IsLine L ∧ k ≤ ((P : Set ℝ²) ∩ L).ncard }.ncard

/--
Given any $n$ points in $\mathbb{R}^2$, the number of $k$-rich lines (lines which contain
$\geq k$ of the points) is, provided $k\leq n^{1/2}$,
$$
\ll \frac{n^2}{k^3}.
$$
-/
@[category research solved, AMS 51 52]
theorem erdos_1069 :
    ∃ C > (0 : ℝ), ∀ (P : Finset ℝ²) (k : ℕ),
      0 < k → (k : ℝ) ≤ (P.card : ℝ) ^ ((1 : ℝ) / 2) →
        (kRichLines P k : ℝ) ≤ C * P.card ^ 2 / k ^ 3 := by
  sorry

end Erdos1069
