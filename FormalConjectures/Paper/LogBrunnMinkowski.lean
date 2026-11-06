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
# The logarithmic Brunn–Minkowski conjecture

*Reference:* OpenAI, *The logarithmic Brunn–Minkowski conjecture* (2026).
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/paper.pdf
-/

@[expose] public section

namespace LogBrunnMinkowski

open MeasureTheory
open scoped InnerProductSpace

local notation "E" n => EuclideanSpace ℝ (Fin n)

open ConvexGeometry

/-- For origin-symmetric convex bodies in $\mathbb{R}^n$ and $0 \leq t \leq 1$,
the logarithmic combination has volume at least $|K|^{1-t}|L|^t$.
No boundary regularity is assumed. -/
@[category research solved, AMS 52,
  formal_proof using lean4 at "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean#L24481"]
theorem log_brunn_minkowski (n : ℕ) (hn : 1 ≤ n) (K L : Set (E n))
    (hK : IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty)
    (hL : IsCompact L ∧ Convex ℝ L ∧ (interior L).Nonempty)
    (hsK : ∀ x, x ∈ K ↔ -x ∈ K) (hsL : ∀ x, x ∈ L ↔ -x ∈ L)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (volume K) ^ (1 - t) * (volume L) ^ t ≤ volume (logCombination K L t) := by
  sorry

end LogBrunnMinkowski
