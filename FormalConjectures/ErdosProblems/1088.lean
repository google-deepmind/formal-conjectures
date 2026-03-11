/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 1088

*Reference:* [erdosproblems.com/1088](https://www.erdosproblems.com/1088)
-/

open scoped EuclideanGeometry

namespace Erdos1088

variable {d : ℕ}

def pairwiseDistancesDistinct (A : Finset (ℝ^d)) : Prop :=
  (A.offDiag.image (fun p : (ℝ^d) × (ℝ^d) => dist p.1 p.2)).card = Nat.choose A.card 2

def hasSubsetWithDistinctDistances (n : ℕ) (S : Finset (ℝ^d)) : Prop :=
  ∃ A : Finset (ℝ^d), A ⊆ S ∧ A.card = n ∧ pairwiseDistancesDistinct A

def cardSet (d n : ℕ) : Set ℕ :=
  { m | ∀ S : Finset (ℝ^d), S.card = m → hasSubsetWithDistinctDistances n S }

noncomputable def f (d n : ℕ) : ℕ := sInf (cardSet d n)

@[category research open, AMS 51]
theorem erdos_1088_general :
    (∀ d ≥ 1, ∀ n ≥ 1, ∃ m, ∀ S : Finset (ℝ^d), S.card = m → hasSubsetWithDistinctDistances n S)
    ↔ answer(sorry) := by
  sorry

@[category research open, AMS 51]
theorem erdos_1088_exponential :
    (∀ d ≥ 3, ∃ c₁ c₂ : ℕ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
      ∀ n ≥ 1, 2 ^ (c₁ * n) ≤ f d n ∧ f d n ≤ 2 ^ (c₂ * n)) ↔ answer(sorry) := by
  sorry

end Erdos1088

