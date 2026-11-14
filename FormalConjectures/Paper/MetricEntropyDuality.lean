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
# A counterexample to metric-entropy duality

*Reference:* OpenAI, *Counterexamples to the duality conjecture for metric entropy*
(2026), Theorem 1.1.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Counterexamples-to-the-duality-conjecture-for-metric-entropy-September-24-2026/main.pdf
-/

@[expose] public section

namespace MetricEntropyDuality

open TranslativeCover
open scoped Pointwise

/-- Every proposed pair $a,b \geq 1$ fails the upper metric-entropy duality bound
for some full-dimensional origin-symmetric convex body and the coordinate cube.
Both covering numbers have finite covers with unrestricted ambient centers. -/
@[category research solved, AMS 46 52]
theorem counterexample (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ n : ℕ, 0 < n ∧ ∃ K : Set (Fin n → ℝ),
      let B : Set (Fin n → ℝ) := {x | ∀ i, |x i| ≤ 1}
      let polar := fun A : Set (Fin n → ℝ) =>
        {y : Fin n → ℝ | ∀ x ∈ A, (∑ i, x i * y i) ≤ 1}
      (IsCompact K ∧ Convex ℝ K ∧ (∀ x, x ∈ K ↔ -x ∈ K) ∧
        (interior K).Nonempty) ∧
      Coverable K B ∧ Coverable (polar B) (a⁻¹ • polar K) ∧
      b * Real.log (coveringNumber (polar B) (a⁻¹ • polar K) : ℝ) <
        Real.log (coveringNumber K B : ℝ) := by
  sorry

end MetricEntropyDuality
