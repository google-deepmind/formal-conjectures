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
# Euclidean Ramsey configurations on a circle

*Reference:* OpenAI, *A classification of finite Euclidean Ramsey configurations* (2026).
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026/paper.pdf
-/

@[expose] public section

namespace EuclideanRamseyCircle

local notation "E" => EuclideanSpace ℝ

/-- Every nonempty configuration of at most five distinct points on a circle is Euclidean
Ramsey: every finite colouring of a suitable Euclidean space has a monochromatic
copy with the same pairwise distances. Singletons and radius-zero circles are included. -/
@[category research solved, AMS 5 52]
theorem at_most_five_circle_points_ramsey {s : ℕ} (a : Fin s → E (Fin 2))
    (hs : 0 < s) (hs5 : s ≤ 5) (ha : Function.Injective a)
    (hsphere : ∃ c : E (Fin 2), ∃ r : ℝ, ∀ i, dist (a i) c = r) :
    ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
      ∀ c : E (Fin D) → Fin r, ∃ b : Fin s → E (Fin D),
        (∀ i j, dist (b i) (b j) = dist (a i) (a j)) ∧
          ∃ k : Fin r, ∀ i, c (b i) = k := by
  sorry

end EuclideanRamseyCircle
