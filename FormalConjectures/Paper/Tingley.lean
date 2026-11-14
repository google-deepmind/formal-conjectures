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
# Tingley's sphere-isometry problem

*Reference:* OpenAI, *A positive solution to Tingley's problem* (2026), Theorem 1.1.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-positive-solution-to-Tingleys-problem-September-23-2026/paper.pdf
-/

@[expose] public section

namespace Tingley

/-- Every surjective isometry between the unit spheres of nonzero real Banach spaces
extends to a surjective real-linear isometry. No finite-dimensionality or separability
assumption is imposed. -/
@[category research solved, AMS 46]
theorem sphere_isometry_extends
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [Nontrivial X] [Nontrivial Y]
    (f : {x : X // ‖x‖ = 1} → {y : Y // ‖y‖ = 1})
    (hf : Isometry f) (hs : Function.Surjective f) :
    ∃ T : X ≃ₗᵢ[ℝ] Y, ∀ u : {x : X // ‖x‖ = 1}, T (u : X) = (f u : Y) := by
  sorry

end Tingley
