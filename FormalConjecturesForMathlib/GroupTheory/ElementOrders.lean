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

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

/-!
# Orders of elements

* `Group.numElementOrders G`: the number of distinct orders of elements of `G`;
* `Group.maxElementOrder G`: the largest order of an element;
* `Group.numInvolutions G`: the number of elements of order `2`.
-/

namespace Group

variable (G : Type*) [Group G]

/-- The number of distinct orders of elements of `G`. -/
noncomputable def numElementOrders : ℕ := (Set.range (orderOf : G → ℕ)).ncard

/-- The largest order of an element of `G` (`0` if the orders are unbounded). -/
noncomputable def maxElementOrder : ℕ := sSup (Set.range (orderOf : G → ℕ))

/-- The number of involutions of `G`, its elements of order `2`. -/
noncomputable def numInvolutions : ℕ := {g : G | orderOf g = 2}.ncard


theorem numInvolutions_le_card [Finite G] : numInvolutions G ≤ Nat.card G :=
  Set.ncard_le_card _

end Group
