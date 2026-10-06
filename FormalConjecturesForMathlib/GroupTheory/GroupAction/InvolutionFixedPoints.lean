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
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

/-!
# Fixed points of involutions

* `MulAction.minInvolutionFixedPoints G α`: the least number of points fixed by an element of
  order at most `2`;
* `MulAction.maxInvolutionFixedPoints G α`: the largest number of points fixed by an involution.

If `G` is the Galois group of a real polynomial acting on its roots, complex conjugation is an
element of order at most `2`, and the number of real roots is the number of points it fixes; so
these bound the number of real roots.
-/

namespace MulAction

variable (G α : Type*) [Group G] [MulAction G α]

/-- The least number of points fixed by an element of order at most `2`; it is `Nat.card α`
if `G` has no involution, since the identity fixes every point. -/
noncomputable def minInvolutionFixedPoints : ℕ :=
  sInf {k : ℕ | ∃ g : G, g ^ 2 = 1 ∧ (fixedBy α g).ncard = k}

/-- The largest number of points fixed by an involution (`0` if `G` has none). -/
noncomputable def maxInvolutionFixedPoints : ℕ :=
  sSup {k : ℕ | ∃ g : G, orderOf g = 2 ∧ (fixedBy α g).ncard = k}


/-- The identity has order at most `2` and fixes every point. -/
theorem minInvolutionFixedPoints_le_card [Finite α] :
    minInvolutionFixedPoints G α ≤ Nat.card α :=
  Nat.sInf_le ⟨1, one_pow 2, by rw [fixedBy_one_eq_univ, Set.ncard_univ]⟩

end MulAction
