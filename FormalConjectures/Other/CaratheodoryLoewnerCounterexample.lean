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

import FormalConjectures.Other.CaratheodoryConjecture

/-!
# The announced smooth counterexamples to the Carathéodory and Loewner conjectures

This file formalises the explicit family announced by Levent Alpöge on 19 August 2026; the
announcement credits John-Paul Smith and Claude with checking the construction. It records the
planar formula and states its smoothness and index properties. The global interpretation of
`counterexample 2` as a support function on the two-sphere is developed from the same formula.

The accompanying file `CaratheodoryLoewnerCounterexample.md` gives a formalisation-oriented
informal proof motivating the statements below.

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

/-- The announced family `g_k` of smooth functions on the complex plane.

The use of the principal complex power chooses a square-root branch when `k` is odd. The seed is
even, so the resulting real-valued expression is independent of the sign of that square root. -/
noncomputable def counterexample (k : ℕ) (z : ℂ) : ℝ :=
  let r := ‖z‖
  let w := Complex.cpow (100 / star z) ((k : ℂ) / 2)
  r ^ 2 * Real.exp (-Real.rpow r (-(1 : ℝ) / 4) * Real.exp (-(r ^ 2))) *
      counterexampleSeed w / (1 + r ^ 2) + 10 ^ 10

/-- Each positive member of the announced family is smooth on the whole complex plane, including
at the origin. The flat exponential factor is essential at the origin. -/
@[category research solved, AMS 26 53]
theorem counterexample_contDiff (k : ℕ) (hk : 0 < k) : ContDiff ℝ ∞ (counterexample k) := by
  sorry

/-- For positive `k`, the origin is an isolated umbilic of principal-line index `1 + k / 2`.

`HasIsolatedZeroIndex` stores twice the principal-line index, hence the integer `2 + k` here. -/
@[category research solved, AMS 26 53 57]
theorem counterexample_hasIsolatedZeroIndex (k : ℕ) (hk : 0 < k) :
    HasIsolatedZeroIndex (traceFreeHessian (counterexample k)) 0 (2 + k) := by
  sorry

/-- Every positive member with `k > 0` violates the index bound in the smooth Loewner
conjecture. -/
@[category research solved, AMS 53 57]
theorem counterexample_not_loewner_bound (k : ℕ) (hk : 0 < k) :
    ¬ ((2 + k : ℕ) : ℤ) ≤ 2 := by
  omega

/- ## The global counterexample on the sphere -/

/-- The north pole used to fix the stereographic chart for the global counterexample. -/
noncomputable def counterexampleNorthPole : sphere (0 : ℝ³) 1 :=
  ⟨EuclideanSpace.single (2 : Fin 3) 1, by
    rw [mem_sphere, dist_zero_right]
    simp⟩

/-- The inverse stereographic chart in which the formula `counterexample 2` is written.

Mathlib's stereographic coordinate has a conventional factor of two. Scaling its target
coordinate by two makes the pullback of the round metric equal to
`4 / (1 + ‖z‖ ^ 2) ^ 2` times the Euclidean metric, as in the accompanying proof. -/
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

/-- **Alpöge's smooth Carathéodory counterexample.**

The function `counterexample 2` extends across the omitted north pole to a smooth function `h`
on the round two-sphere. It is the support function of a convex body `K`; `F` is its smooth
Gauss parametrization with outward normal `p`. The corresponding convex surface has exactly one
umbilic, at the point represented by `z = 0`.

The explicit compactness and nonempty-interior conditions rule out unbounded and
lower-dimensional convex sets. The range equality ensures that `F` parametrizes the boundary
of the same body whose support function is `h`. -/
@[category research solved, AMS 52 53]
theorem counterexample_two_is_support_function_with_unique_umbilic :
    ∃ (h : sphere (0 : ℝ³) 1 → ℝ) (F : sphere (0 : ℝ³) 1 → ℝ³) (K : Set ℝ³),
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h ∧
      (∀ z : ℂ, h (counterexampleSphereChart z) = counterexample 2 z) ∧
      IsConvexSphereOfClass ∞ F (fun p ↦ (p : ℝ³)) ∧
      Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧
      Set.range F = frontier K ∧ IsSupportParametrization h F K ∧
      IsUmbilic F (fun p ↦ (p : ℝ³)) (counterexampleSphereChart 0) ∧
      ∀ p, IsUmbilic F (fun q ↦ (q : ℝ³)) p → p = counterexampleSphereChart 0 := by
  sorry

end CaratheodoryLoewnerCounterexample
