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
# A product counterexample to Brannen's simplex maximum

*Reference:* OpenAI, *A product counterexample to the simplex maximum for
projection-body volume* (2026), Theorem 1.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-product-counterexample-to-the-simplex-maximum-for-projection-body-volume-September-24-2026/paper.pdf

Witness and statement adapted from the Apache-2.0
[ProjectionVolume comparator](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ProjectionVolume.lean).
The simplex and block maps are inlined, and only the body and exact-ratio conclusions are retained.
-/

@[expose] public section

namespace BrannenProjectionVolume

open scoped InnerProductSpace

/-- The product of two coordinate ten-dimensional simplices in twenty-space. -/
def productWitness : Set (EuclideanSpace ℝ (Fin 20)) :=
  let Δ := convexHull ℝ (insert 0
    (Set.range fun i : Fin 10 => EuclideanSpace.single i (1 : ℝ)))
  {x | WithLp.toLp 2 (fun i : Fin 10 => x (Fin.castAdd 10 i)) ∈ Δ ∧
    WithLp.toLp 2 (fun i : Fin 10 => x (Fin.natAdd 10 i)) ∈ Δ}

/-- The product of two ten-dimensional simplices has normalized projection volume
$22355476/22020096$ times the twenty-dimensional simplex value, so simplices do not
maximize this functional in dimension twenty. -/
@[category research solved, AMS 52]
theorem product_counterexample :
    let projection : Set (EuclideanSpace ℝ (Fin 20)) :=
      {y | ∀ u : EuclideanSpace ℝ (Fin 20),
        let H := (Submodule.span ℝ {u})ᗮ
        ⟪u, y⟫_ℝ ≤ ‖u‖ *
          (MeasureTheory.volume : MeasureTheory.Measure H).real
            (H.orthogonalProjectionOnto '' productWitness)}
    (IsCompact productWitness ∧ Convex ℝ productWitness ∧
      (interior productWitness).Nonempty) ∧
    (MeasureTheory.volume.real projection / MeasureTheory.volume.real productWitness ^ 19) /
      ((21 : ℝ) * (20 : ℝ) ^ 20 / Nat.factorial 20) =
      (22355476 : ℝ) / 22020096 := by
  sorry

/-- The explicit normalized ratio exceeds one. -/
@[category test, AMS 52]
theorem ratio_gt_one : (1 : ℝ) < 22355476 / 22020096 := by
  norm_num

end BrannenProjectionVolume
