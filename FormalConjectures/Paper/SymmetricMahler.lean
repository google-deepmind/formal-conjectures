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
# The symmetric Mahler conjecture

*Reference:* OpenAI, *The symmetric Mahler conjecture and its equality cases* (2026).
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/paper.pdf
-/

@[expose] public section

namespace SymmetricMahler

open MeasureTheory

open ConvexGeometry

/-- Every origin-symmetric convex body $K \subset \mathbb{R}^n$ in positive dimension
satisfies $|K|\,|K^\circ| \geq 4^n/n!$. Volume is ordinary Lebesgue measure.
No smoothness assumptions are imposed. -/
@[category research solved, AMS 52]
theorem symmetric_mahler {n : ℕ} (hn : 1 ≤ n) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K)
    (hint : (interior K).Nonempty) :
    (4 : ℝ) ^ n / n.factorial ≤ (volume K).toReal * (volume (coordinatePolar K)).toReal := by
  sorry

end SymmetricMahler
