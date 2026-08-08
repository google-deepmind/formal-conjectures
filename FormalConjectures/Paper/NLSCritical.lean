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
# Energy-critical NLS in three dimensions.

This file states an a priori estimate for the energy-critical nonlinear Schrödinger equation on $ℝ^3$.
By 'soft' arguments, this bound implies global well-posedness in the energy space, scattering,
asymptotic completeness, and uniform regularity (all of which are less elementary to state).
This is remarked on p. 770 and p. 793 in the referenced article which first proved the a priori bound.

The main theorem is:
- `NLS_apriori`: a bound on the space-time $L^10$ norm in terms of the initial energy for local
  smooth solutions to the NLS equation.

## References
* [Colliander, Keel, Staffilani, Takaoka, Tao](https://doi.org/10.4007/annals.2008.167.767),
  Annals of Mathematics 167 (2008) proves the a priori estimate, and thereby, global well-posedness.
-/

open Set ContDiff EuclideanGeometry Laplacian

namespace NLSCritical

/--
A smooth solution to the NLS equation on the time interval $[-l, l]$.
We additionally require that $x ↦ u(t,x)$ is Schwartz for all $t$ in the interval.
-/
structure LocalSchwartzSolution (l : ℝ) where
  u : ℝ → ℝ^3 → ℂ
  smooth : ContDiffOn ℝ ∞ (Function.uncurry u) (Icc (-l) l ×ˢ univ)
  schwartz : ∀ t ∈ Icc (-l) l, ∃ f : (SchwartzMap (ℝ^3) ℂ), u t = f
  solution : ∀ t ∈ Icc (-l) l, ∀ x, Complex.I * (deriv (u · x) t) + Δ (u t) x = ‖u t x‖^4 * (u t x)

/--
The Hamiltonian of the energy-critical NLS in $ℝ^3$.
-/
noncomputable def energy (u : ℝ^3 → ℂ) : ℝ :=
  ∫ x, (1 / 2) * ‖fderiv ℝ u x‖^2 + (1 / 6) * ‖u x‖^6

/--
The space-time $L^10$ norm, restricted to the time interval $[-l,l]$.
-/
noncomputable def L10_local (l : ℝ) (u : ℝ → ℝ^3 → ℂ) :=
  ∫ t in Icc (-l) l, (∫ x, ‖u t x‖^10)

/--
The $L^10_{t,x}$ a priori estimate for local schwartz solutions.
-/
@[category research solved, AMS 35]
theorem NLS_apriori :
    ∃ f : ℝ → ℝ, ∀ l > 0, ∀ s : LocalSchwartzSolution l,
    L10_local l s.u ≤ f (energy (s.u 0)) := by
  sorry

end NLSCritical
