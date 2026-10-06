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
`α` is `k`-transitive (`MulAction.IsMultiplyPretransitive`). Every action is `k`-transitive for
`k > Nat.card α`, as there are no injections `Fin k ↪ α`, hence the bound.
-/

namespace MulAction

variable (G α : Type*) [Group G] [MulAction G α]

/-- The largest `k ≤ Nat.card α` such that the action is `k`-transitive. -/
noncomputable def transitivityDegree : ℕ :=
  sSup {k : ℕ | k ≤ Nat.card α ∧ IsMultiplyPretransitive G α k}


theorem transitivityDegree_le_card [Finite α] : transitivityDegree G α ≤ Nat.card α :=
  csSup_le' fun _ hk => hk.1

end MulAction
