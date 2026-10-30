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
# Petty's projection-volume conjecture

*Reference:* OpenAI, *Petty's projection-volume conjecture in dimensions at least
four* (2026), Theorem 1.1.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Pettys-projection-volume-conjecture-in-dimensions-at-least-four-September-24-2026/paper.pdf
-/

@[expose] public section

namespace PettyProjectionVolume

open MeasureTheory ConvexGeometry

/-- Every convex body in dimension $n \geq 4$ satisfies
$|\Pi K|/|K|^{n-1} \geq \kappa_{n-1}^n\kappa_n^{2-n}$, where $\kappa_j$ is the
volume of the Euclidean unit ball. Equality holds exactly for ellipsoids.
No symmetry or boundary regularity is assumed. -/
@[category research solved, AMS 52]
theorem petty_projection_volume (n : ℕ) (hn : 4 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty) :
    let κ := fun j : ℕ => volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin j)) 1)
    κ (n - 1) ^ n * κ n ^ (2 - (n : ℤ)) ≤ projectionRatio K ∧
      (projectionRatio K = κ (n - 1) ^ n * κ n ^ (2 - (n : ℤ)) ↔
        ∃ (a : EuclideanSpace ℝ (Fin n))
          (T : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)),
          K = (fun x => a + T x) '' Metric.closedBall 0 1) := by
  sorry

end PettyProjectionVolume
