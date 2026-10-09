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
# A doubling Hilbert subset without finite-dimensional embedding

*Reference:* OpenAI, *A doubling Hilbert subset with no finite-dimensional
bi-Lipschitz embedding* (2026), Theorem 1.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-doubling-Hilbert-subset-with-no-finite-dimensional-bi-Lipschitz-embedding-September-25-2026/main.pdf
-/

@[expose] public section

namespace DoublingHilbert

/-- There is a fixed subset of real $\ell_2$ with intrinsic open-ball doubling
constant at most $76800$ and no bi-Lipschitz embedding into any positive-dimensional
Euclidean space, at any finite distortion or positive scale. -/
@[category research solved, AMS 46 54]
theorem no_finite_dimensional_embedding :
    ∃ S : Set (lp (fun _ : ℕ => ℝ) 2),
      (∀ x : S, ∀ r : ℝ, 0 < r →
        ∃ centers : Finset S, centers.card ≤ 76800 ∧
          ∀ y : S, dist y x < r → ∃ c ∈ centers, dist y c < r / 2) ∧
      ∀ k : ℕ, 0 < k →
        ¬ ∃ f : S → EuclideanSpace ℝ (Fin k),
          ∃ a : ℝ, 0 < a ∧ ∃ D : ℝ, 1 ≤ D ∧
            ∀ x y : S, a * dist x y ≤ dist (f x) (f y) ∧
              dist (f x) (f y) ≤ D * a * dist x y := by
  sorry

end DoublingHilbert
