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
# Tao's Optimization Constant 39 / Hadwiger covering / illumination number in $\mathbb{R}^3$

The least number of translates of the interior sufficient to cover every three-dimensional
convex body. A universal finite covering bound is known, so the constant is a natural number.

*References:*
- [Tao's Optimization Constant 39](https://teorth.github.io/optimizationproblems/constants/39a.html)
- [ABP2024] Arman, A.; Bondarenko, A.; Prymak, A., *On Hadwiger's covering problem in small
  dimensions*, Canadian Mathematical Bulletin 68 (2025), 1239–1250.
  https://doi.org/10.4153/S0008439525000384
- [Pap1999] Papadoperakis, I., *An estimate for the problem of illumination of the boundary
  of a convex body in E³*, Geometriae Dedicata 75 (1999), 275–285.
  https://doi.org/10.1023/A:1005056207406
- [Pry2023] Prymak, A., *A new bound for Hadwiger's covering problem in E³*, SIAM Journal on
  Discrete Mathematics 37 (2023), 17–24. https://doi.org/10.1137/22M1490314
-/

namespace Constant39

open Set

open scoped EuclideanGeometry

/-- Every convex body with nonempty interior in three-dimensional Euclidean space is covered by `n`
translates of its interior. -/
def CoversConvexBodies (n : ℕ) : Prop :=
  ∀ K : ConvexBody (ℝ^3), (interior (K : Set (ℝ^3))).Nonempty → ∃ v : Fin n → ℝ^3,
    (K : Set (ℝ^3)) ⊆ ⋃ i, (fun x ↦ v i + x) '' interior (K : Set (ℝ^3))

/-- **Tao's Optimization Constant 39 / Hadwiger covering / illumination number in
$\mathbb{R}^3$**.

The smallest number `n` such that every 3-dimensional convex body with nonempty interior can be
covered by `n` translates of its interior. -/
noncomputable def C39 : ℕ := sInf {n | CoversConvexBodies n}

/-- Any universal covering number is an upper bound for `C39`. -/
@[category API, AMS 52]
theorem c39_le_of_covers {n : ℕ} (hn : CoversConvexBodies n) : C39 ≤ n :=
  csInf_le' hn

/-- The first recorded and current best known lower bound, given by the cube; see [ABP2024]. -/
@[category research solved, AMS 52]
theorem c39_lower_bound : 8 ≤ C39 := by
  sorry

/-- Can the current best lower bound be improved? -/
@[category research open, AMS 52]
theorem c39_lower_bound_improved : answer(sorry) ↔ 8 < C39 := by
  sorry

/-- The first recorded upper bound, proved by Papadoperakis [Pap1999] using illumination of
three-dimensional convex bodies. -/
@[category research solved, AMS 52]
theorem c39_le_16 : C39 ≤ 16 := by
  sorry

/-- The current best known upper bound, proved by Prymak [Pry2023] using a covering argument
with computer-assisted verification. -/
@[category research solved, AMS 52]
theorem c39_upper_bound : C39 ≤ 14 := by
  sorry

/-- Can the current best upper bound be improved? -/
@[category research open, AMS 52]
theorem c39_upper_bound_improved : answer(sorry) ↔ C39 < 14 := by
  sorry

end Constant39
