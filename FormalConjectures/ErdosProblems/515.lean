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
# Erdős Problem 515

*References:*
- [erdosproblems.com/515](https://www.erdosproblems.com/515)
- [LRW84] Lewis, John, Rossi, John, and Weitsman, Allen,
  _On the growth of subharmonic functions along paths_. Ark. Mat. (1984), 109–119.
- Path and integral definitions follow the Apache 2.0 formalization at
  https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos515/Path.lean
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace Erdos515

/-- An affine parametrization of the segment from `a` to `b`. -/
noncomputable def segmentPoint (a b : ℂ) (t : ℝ) : ℂ :=
  AffineMap.lineMap a b t

/-- A polygonal ray whose entire segments escape every bounded set. Each segment is rectifiable,
so its constant-speed continuous parametrization is locally rectifiable. -/
structure PolygonalRay where
  vertex : ℕ → ℂ
  tendsToInfinity : ∀ R : ℝ, ∃ N : ℕ, ∀ n ≥ N,
    ∀ t ∈ Icc (0 : ℝ) 1, R ≤ ‖segmentPoint (vertex n) (vertex (n + 1)) t‖

/-- The inverse-modulus density, with infinite value at a zero when `lambda > 0`. -/
noncomputable def inverseNormDensity (f : ℂ → ℂ) (lambda : ℝ) (a b : ℂ) (t : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖f (segmentPoint a b t)‖) ^ (-lambda)

/-- The nonnegative arclength integral on one affine segment. -/
noncomputable def segmentIntegral (f : ℂ → ℂ) (lambda : ℝ) (a b : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ‖b - a‖ *
    ∫⁻ t in Icc (0 : ℝ) 1, inverseNormDensity f lambda a b t

/-- The nonnegative arclength integral on a polygonal ray. -/
noncomputable def lineIntegral (C : PolygonalRay) (f : ℂ → ℂ) (lambda : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, segmentIntegral f lambda (C.vertex n) (C.vertex (n + 1))

/--
Let $f(z)$ be an entire function, not a polynomial. Does there exist a locally rectifiable path
$C$ tending to infinity such that, for every $\lambda>0$, the integral
$\int_C \lvert f(z)\rvert^{-\lambda}\,\mathrm{d}s$ is finite?

The general case was proved by Lewis, Rossi, and Weitsman [LRW84], who in fact proved this
with $\lvert f\rvert$ replaced by $e^u$ where $u$ is any subharmonic function.
This formulation records the stronger conclusion that the path can be a polygonal ray.
-/
@[category research solved, AMS 30]
theorem erdos_515 : answer(True) ↔ ∀ f : ℂ → ℂ, Differentiable ℂ f →
    (¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = f z) →
    ∃ C : PolygonalRay, ∀ lambda : ℝ, 0 < lambda → lineIntegral C f lambda ≠ ⊤ := by
  sorry

end Erdos515
