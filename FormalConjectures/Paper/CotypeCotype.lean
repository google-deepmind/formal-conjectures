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
# The cotype–cotype conjecture under the approximation property

*Reference:* OpenAI, *The cotype–cotype conjecture under the approximation property*
(2026), Theorem 1.1.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-cotype-cotype-conjecture-under-the-approximation-property-September-23-2026/paper.pdf
-/

@[expose] public section

namespace CotypeCotype

open RademacherCotype

/-- A nonzero real Banach space with the ordinary approximation property is
$K$-convex exactly when it and its continuous dual have finite Rademacher cotype.
The two cotype exponents may differ; no bounded approximation property is required. -/
@[category research solved, AMS 46]
theorem cotype_cotype (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [Nontrivial X] (hAP : ApproximationProperty X) :
    KConvex X ↔ FiniteCotype X ∧ FiniteCotype (X →L[ℝ] ℝ) := by
  sorry

end CotypeCotype
