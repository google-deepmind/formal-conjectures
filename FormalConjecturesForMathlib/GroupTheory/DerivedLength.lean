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

public import Mathlib.GroupTheory.Solvable
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Derived length

`Group.derivedLength G` is the length of the derived series of `G`: the least `k` with
`derivedSeries G k = ⊥`, which exists exactly when `G` is solvable (`Group.IsSolvable`).
-/

namespace Group

variable (G : Type*) [Group G]

/-- The derived length of `G`: the least `k` with `derivedSeries G k = ⊥`. It is `0` if there is
none, that is, if `G` is not solvable. -/
noncomputable def derivedLength : ℕ := sInf {k : ℕ | derivedSeries G k = ⊥}


theorem derivedLength_of_not_isSolvable (h : ¬ IsSolvable G) : derivedLength G = 0 := by
  have : {k : ℕ | derivedSeries G k = ⊥} = ∅ :=
    Set.eq_empty_of_forall_notMem fun k hk => h ⟨⟨k, hk⟩⟩
  simp [derivedLength, this]

theorem derivedLength_of_subsingleton [Subsingleton G] : derivedLength G = 0 :=
  Nat.sInf_eq_zero.mpr (Or.inl (by simpa using Subgroup.eq_bot_of_subsingleton ⊤))

end Group
