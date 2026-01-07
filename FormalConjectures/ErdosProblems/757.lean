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

*Reference:*
 - [erdosproblems.com/757](https://www.erdosproblems.com/757)
 - [Er49d] Erdös, P. "On the strong law of large numbers." Transactions of the American Mathematical
    Society 67.1 (1949): 51-56.
 - [Ma66] Matsuyama, Noboru. "On the strong law of large numbers." Tohoku Mathematical Journal,
    Second Series 18.3 (1966): 259-269.
-/

open scoped Pointwise
open Filter

/-- Let `B` be a Sidon set `B` of size 4. Then `(B - B).ncard = 13`. -/
@[category research open, AMS 5]
theorem IsSido.sub_card {B : Set ℝ} (hn : B.ncard = 4) (hpos : ∀ x ∈ B, 0 < x)
    (hB : IsSidon B) : (B - B).ncard = 13 := by
  sorry

namespace Erdos757

/-- Sth . -/
@[category research open, AMS 5]
theorem erdos_757 {A : Set ℝ} :
    answer(sorry) = sInf {c | ∀ {A : Set ℝ}, A.Finite → (∀ x ∈ A, 0 < x) → (∀ B ⊆ A,
    B.ncard = 4 → (B - B).ncard = 11) → ∃ S ⊆ A, IsSidon S ∧ c * A.ncard ≤ (S.ncard : ℝ)} := by
  sorry

/-- Sth . -/
@[category research solved, AMS 5]
theorem erdos_757.lowerBound {A : Set ℝ} : 1 / (2 : ℝ) <
    sInf {c | ∀ {A : Set ℝ}, A.Finite → (∀ x ∈ A, 0 < x) → (∀ B ⊆ A,
    B.ncard = 4 → (B - B).ncard = 11) → ∃ S ⊆ A, IsSidon S ∧ c * A.ncard ≤ (S.ncard : ℝ)} := by
  sorry

/-- Sth . -/
@[category research solved, AMS 5]
theorem erdos_757.upperBound {A : Set ℝ} : sInf {c | ∀ {A : Set ℝ}, A.Finite → (∀ x ∈ A, 0 < x) →
    (∀ B ⊆ A, B.ncard = 4 → (B - B).ncard = 11) → ∃ S ⊆ A, IsSidon S ∧
    c * A.ncard ≤ (S.ncard : ℝ)} < 3 / (5 : ℝ) := by
  sorry

end Erdos757
