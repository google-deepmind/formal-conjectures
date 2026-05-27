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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 287

*Reference:* [erdosproblems.com/287](https://www.erdosproblems.com/287)

Let `k ≥ 2`.  Is it true that, for any distinct integers
`n₁ < ⋯ < n_k` with `1 = 1 / n₁ + ⋯ + 1 / n_k`, one must have
`max_i (n_{i+1} - n_i) ≥ 3`?

We formulate the denominators as positive natural numbers and evaluate the
reciprocal sum in `ℚ`.
-/

noncomputable section

namespace Erdos287

open scoped BigOperators

/-- The denominators are positive and strictly increasing with the index. -/
def StrictPositiveIncreasing {k : ℕ} (n : Fin k → ℕ) : Prop :=
  (∀ i : Fin k, 0 < n i) ∧
    ∀ i j : Fin k, i.val < j.val → n i < n j

/-- The reciprocal sum condition `∑ i, 1 / n_i = 1`. -/
def ReciprocalSumOne {k : ℕ} (n : Fin k → ℕ) : Prop :=
  (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = 1

/-- Some consecutive gap is at least `3`. -/
def HasGapAtLeastThree {k : ℕ} (n : Fin k → ℕ) : Prop :=
  ∃ i j : Fin k, j.val = i.val + 1 ∧ 3 ≤ n j - n i

/-- Erdős problem 287, formulated for positive increasing denominators. -/
def Erdos287Conjecture : Prop :=
  ∀ k : ℕ,
    2 ≤ k →
      ∀ n : Fin k → ℕ,
        StrictPositiveIncreasing n →
          ReciprocalSumOne n →
            HasGapAtLeastThree n

/--
If `1 = 1 / n₁ + ⋯ + 1 / n_k` with `n₁ < ⋯ < n_k`, must some consecutive gap
be at least `3`?
-/
@[category research open, AMS 11]
theorem erdos_287 : answer(sorry) ↔ Erdos287Conjecture := by
  sorry

end Erdos287

end

