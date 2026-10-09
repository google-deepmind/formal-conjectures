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
# Nonexpansive fixed points in reflexive Banach spaces

*Reference:* OpenAI, *Fixed Points of Nonexpansive Maps in Reflexive Banach Spaces*
(2026), Theorem 1.1.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Fixed-Points-of-Nonexpansive-Maps-in-Reflexive-Banach-Spaces-September-24-2026/paper.pdf
-/

@[expose] public section

namespace ReflexiveFixedPoints

/-- Every nonexpansive selfmap of a nonempty closed bounded convex subset of a real
reflexive Banach space has a fixed point in the given norm. Reflexivity is stated as
surjectivity of the canonical map into the continuous bidual. -/
@[category research solved, AMS 46 47]
theorem exists_fixedPoint
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X))
    (C : Set X) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hconvex : Convex ℝ C)
    (F : C → C)
    (hF : ∀ a b : C, ‖(F a : X) - (F b : X)‖ ≤ ‖(a : X) - (b : X)‖) :
    ∃ a : C, F a = a := by
  sorry

end ReflexiveFixedPoints
