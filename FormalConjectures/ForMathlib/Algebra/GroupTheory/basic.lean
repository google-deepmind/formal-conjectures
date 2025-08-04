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

import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PresentedGroup

open MulAut Subgroup

/--
An automorphism is regular if its fixed points are trivial.
-/
def IsRegularAut (G : Type*) [Group G] (φ : MulAut G) : Prop := ∀ g : G, φ g = g → g = 1

namespace Group

/--
A group is finitely presented if it has a finite presentation.
-/
class FinitelyPresented (G : Type*) [Group G] : Prop where
  finitely_presented : ∃ (ι : Type*) (rels : Finset (FreeGroup ι)),
    Nonempty (G ≃* PresentedGroup (rels : Set (FreeGroup ι)))

/--
A group is metabelian if it has an abelian normal subgroup with abelian quotient.
-/
class Metabelian (G : Type*) [Group G] : Prop :=
  metabelian : derivedSeries G 2 = ⊥

/-! ## Local conditions -/

/--
A group is locally finite if every finitely generated subgroup is finite.
-/
def LocallyFinite (G : Type*) [Group G] : Prop :=
  ∀ (H : Subgroup G), FG H → Finite H

/--
A group is locally solvable if every finitely generated subgroup is solvable.
-/
def LocallySolvable (G : Type*) [Group G] : Prop :=
  ∀ (H : Subgroup G), FG H → IsSolvable H

/--
A group is locally nilpotent if every finitely generated subgroup is nilpotent.
-/
def LocallyNilpotent (G : Type*) [Group G] : Prop :=
  ∀ (H : Subgroup G), FG H → IsNilpotent H

/-! ## Relations on groups -/

/--
A relation is right-invariant if it is preserved under right multiplication.
-/
class RightInvariantRel (G : Type*) [Mul G] (r : G → G → Prop) : Prop where
  right_invariant : ∀ {a b : G}, r a b → ∀ c, r (a * c) (b * c)

/--
A group is right orderable if exists a total order preserved under right multiplication.
-/
def RightOrderable (G : Type*) [Group G] : Prop :=
  ∃ (l : G → G → Prop), IsLinearOrder G l ∧ RightInvariantRel G l

/--
A group is pro-orderable if every right-invariant partial order extends to a linear order.
-/
def ProOrderable (G : Type*) [Group G] : Prop :=
  ∀ (r : G → G → Prop) [IsPartialOrder G r] [RightInvariantRel G r], ∃ (l : G → G → Prop),
  IsLinearOrder G l ∧ RightInvariantRel G l ∧ (∀ a b, r a b → l a b)

end Group
