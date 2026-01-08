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
# Erdős Problem 757

*References:*
 - [erdosproblems.com/757](https://www.erdosproblems.com/757)
 - [GyLe95] Gyárfás, András and Lehel, Jenő, Linear sets with five distinct differences among any
    four elements. J. Combin. Theory Ser. B (1995), 108-118.
-/

open scoped Pointwise
open Filter

namespace Erdos757

/-- We say that `c` is admissible if for any finit set `A` such that for any subset `B` of size `4`,
`(B - B).card = 11`, there exists a Sidon subset `S` of size at least `c * A.ncard`. -/
def IsAdmissible (c : ℝ) : Prop := ∀ {A : Set ℝ}, A.Finite → (∀ B ⊆ A,
  B.ncard = 4 → (B - B).ncard = 11) → ∃ S ⊆ A, IsSidon S ∧ c * A.ncard ≤ (S.ncard : ℝ)

/-- What is the supremum of the set of admissible numbers? -/
@[category research open, AMS 5]
theorem erdos_757 {A : Set ℝ} :
    answer(sorry) = sSup {c | IsAdmissible c} := by
  sorry

/-- The supremum is strictly larger than `1 / 2`, which is proved in [GyLe95]. -/
@[category research solved, AMS 5]
theorem erdos_757.lowerBound {A : Set ℝ} : 1 / (2 : ℝ) < sSup {c | IsAdmissible c} := by
  sorry

/-- In [GyLe95], the authors also prove that the supremum is smaller than `3 / 5`. -/
@[category research solved, AMS 5]
theorem erdos_757.upperBound {A : Set ℝ} : sSup {c | IsAdmissible c} < 3 / (5 : ℝ) := by
  sorry

end Erdos757
