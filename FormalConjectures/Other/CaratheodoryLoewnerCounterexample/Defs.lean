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
import FormalConjectures.Other.CaratheodoryConjecture

/-!
# Definitions for the announced smooth Carathéodory–Loewner counterexamples

This file records the explicit planar family, its stereographic chart, and the support-function
predicate used in the counterexample announced by Levent Alpöge on 19 August 2026.

*Reference:*
- [L. Alpöge, X post 2089971359921156203](https://x.com/__alpoge__/status/2089971359921156203)
-/

open scoped ContDiff EuclideanGeometry Manifold
open Set Metric

namespace CaratheodoryLoewnerCounterexample

open CaratheodoryConjecture LoewnerConjecture

/-- The periodic real-valued function used in the announced counterexample. -/
noncomputable def counterexampleSeed (z : ℂ) : ℝ :=
  -Real.cos (2 * z.re) / 4 + 3 * Real.cos (2 * z.im) / 10 -
    Real.cos (4 * z.im) / 32 + Real.sin z.re * Real.sin z.im

/-- The seed is invariant under the sign ambiguity of a square root. -/
@[category API, AMS 26]
theorem counterexampleSeed_neg (z : ℂ) : counterexampleSeed (-z) = counterexampleSeed z := by
  simp [counterexampleSeed]

/-- The announced family `g_k` of smooth functions on the complex plane.

The use of the principal complex power chooses a square-root branch when `k` is odd. The seed is
even, so the resulting real-valued expression is independent of the sign of that square root. -/
noncomputable def counterexample (k : ℕ) (z : ℂ) : ℝ :=
  let r := ‖z‖
  let w := Complex.cpow (100 / star z) ((k : ℂ) / 2)
  r ^ 2 * Real.exp (-Real.rpow r (-(1 : ℝ) / 4) * Real.exp (-(r ^ 2))) *
      counterexampleSeed w / (1 + r ^ 2) + 10 ^ 10

/-- Every member of the family takes the constant support value at the origin. -/
@[category API, AMS 26]
theorem counterexample_zero (k : ℕ) : counterexample k 0 = 10 ^ 10 := by
  simp [counterexample]

/-- The north pole used to fix the stereographic chart for the global counterexample. -/
noncomputable def counterexampleNorthPole : sphere (0 : ℝ³) 1 :=
  ⟨EuclideanSpace.single (2 : Fin 3) 1, by
    rw [mem_sphere, dist_zero_right]
    simp⟩

/-- The inverse stereographic chart in which the formula `counterexample 2` is written.

Mathlib's stereographic coordinate has a conventional factor of two. Scaling its target
coordinate by two makes the pullback of the round metric equal to
`4 / (1 + ‖z‖ ^ 2) ^ 2` times the Euclidean metric. -/
noncomputable def counterexampleSphereChart (z : ℂ) : sphere (0 : ℝ³) 1 :=
  letI : Fact (Module.finrank ℝ ℝ³ = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩
  (stereographic' 2 counterexampleNorthPole).symm
    (2 • Complex.orthonormalBasisOneI.repr z)

/-- The origin of the planar chart represents the south pole. This test fixes the scale and sign
convention in `counterexampleSphereChart`. -/
@[category test, AMS 53]
theorem counterexampleSphereChart_zero :
    counterexampleSphereChart 0 = -counterexampleNorthPole := by
  apply Subtype.ext
  simp [counterexampleSphereChart, stereographic'_symm_apply]

/-- `F` parametrizes the supporting point of `K` with outer unit normal `p`, and `h p` is
the corresponding support value.

The final inequality says that the hyperplane through `F p` perpendicular to `p` supports
the whole body. Requiring `F p ∈ K` makes the supremum attained and avoids conventions for
`sSup ∅`. -/
def IsSupportParametrization (h : sphere (0 : ℝ³) 1 → ℝ)
    (F : sphere (0 : ℝ³) 1 → ℝ³) (K : Set ℝ³) : Prop :=
  ∀ p, F p ∈ K ∧ inner ℝ (F p) (p : ℝ³) = h p ∧
    ∀ x ∈ K, inner ℝ x (p : ℝ³) ≤ h p

end CaratheodoryLoewnerCounterexample
