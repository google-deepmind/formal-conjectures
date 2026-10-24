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
# A separable quotient counterexample under the continuum hypothesis

*Reference:* OpenAI, *Relative independence of the separable quotient problem*
(2026), Theorem 1.1, negative direction.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-independence-of-the-separable-quotient-problem-September-23-2026/paper.pdf
-/

@[expose] public section

namespace SeparableQuotient

/-- Under the continuum hypothesis, some infinite-dimensional real Banach space
has no bounded linear surjection onto any infinite-dimensional separable real
Banach space. This states the conditional counterexample, not relative independence. -/
@[category research solved, AMS 3 46]
theorem real_counterexample_of_CH (hCH : Cardinal.mk ℝ = Cardinal.aleph 1) :
    ¬ ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
      (¬ FiniteDimensional ℝ X) →
        ∃ (Y : Type) (_ : NormedAddCommGroup Y) (_ : NormedSpace ℝ Y),
          CompleteSpace Y ∧ TopologicalSpace.SeparableSpace Y ∧
            (¬ FiniteDimensional ℝ Y) ∧
            ∃ T : X →L[ℝ] Y, Function.Surjective T := by
  sorry

end SeparableQuotient
