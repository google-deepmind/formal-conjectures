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

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Order.Atoms

@[expose] public section

/-!
# Numbers of subgroups

* `Group.numNormalSubgroups G`: the number of normal subgroups of `G`;
* `Group.numMaximalSubgroupClasses G`: the number of conjugacy classes of maximal subgroups.
-/

open scoped Pointwise

namespace Group

variable (G : Type*) [Group G]

/-- The number of normal subgroups of `G`. -/
noncomputable def numNormalSubgroups : ℕ := {H : Subgroup G | H.Normal}.ncard

/-- The number of conjugacy classes of maximal subgroups of `G`. -/
noncomputable def numMaximalSubgroupClasses : ℕ :=
  ((fun H : Subgroup G => MulAction.orbit (ConjAct G) H) '' {H : Subgroup G | IsCoatom H}).ncard


theorem numNormalSubgroups_pos [Finite G] : 0 < numNormalSubgroups G := by
  have : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨⊥, Subgroup.normal_bot⟩

end Group
