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

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

@[expose] public section

/-!
# The degree of transitivity

`MulAction.transitivityDegree G α` is the largest `k ≤ Nat.card α` such that the action of `G` on
`α` is `k`-transitive (`MulAction.IsMultiplyPretransitive`). For finite `α`, every action is
`k`-transitive for `k > Nat.card α`, because there is no injection `Fin k ↪ α`; hence the bound.
For infinite `α`, `Nat.card α = 0`, so `transitivityDegree G α = 0`
(`transitivityDegree_of_infinite`).
-/

namespace MulAction

variable (G α : Type*) [Group G] [MulAction G α]

/-- The largest `k ≤ Nat.card α` such that the action is `k`-transitive; it is `0` for infinite
`α`. -/
noncomputable def transitivityDegree : ℕ :=
  sSup {k : ℕ | k ≤ Nat.card α ∧ IsMultiplyPretransitive G α k}


theorem transitivityDegree_le_card [Finite α] : transitivityDegree G α ≤ Nat.card α :=
  csSup_le' fun _ hk => hk.1

/-- For infinite `α`, `Nat.card α = 0`, so the degree is `0`. -/
theorem transitivityDegree_of_infinite [Infinite α] : transitivityDegree G α = 0 :=
  Nat.eq_zero_of_le_zero <| csSup_le' fun _ hk => by
    simpa [Nat.card_eq_zero_of_infinite] using hk.1

end MulAction
