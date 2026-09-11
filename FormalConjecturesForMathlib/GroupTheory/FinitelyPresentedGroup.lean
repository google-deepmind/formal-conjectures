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

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.PresentedGroup

import Mathlib.Tactic

/-!
# Finitely presented groups

A group is *finitely presented* if it is isomorphic to a group given by a finite
presentation $\langle x_1, \dots, x_n \mid r_1, \dots, r_m \rangle$.

Mathlib has `Group.IsFinitelyPresented` in `Mathlib.GroupTheory.FinitelyPresentedGroup`
(added 2026-03), defined via a surjection from a free group with finitely normally generated
kernel; `Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup` shows it agrees with the
definition here. That file postdates the mathlib version pinned by this repository, so this is
a stand-in to be deleted once the pin moves past it.
-/

@[expose] public section

namespace Group

/-- A group $G$ is *finitely presented* if it is isomorphic to a group given by a
finite presentation $\langle x_1, \dots, x_n \mid r_1, \dots, r_m \rangle$, i.e. the
quotient of the free group on $n$ generators by the normal closure of a finite set of
relators. -/
def IsFinitelyPresented (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (rels : Finset (FreeGroup (Fin n))),
    Nonempty (PresentedGroup (rels : Set (FreeGroup (Fin n))) ≃* G)

/-- A group given by a finite presentation is finitely presented. -/
lemma isFinitelyPresented_presentedGroup (n : ℕ) (rels : Finset (FreeGroup (Fin n))) :
    IsFinitelyPresented (PresentedGroup (rels : Set (FreeGroup (Fin n)))) :=
  ⟨n, rels, ⟨MulEquiv.refl _⟩⟩

namespace IsFinitelyPresented

variable {G H : Type*} [Group G] [Group H]

/-- Finite presentability is invariant under group isomorphism. -/
lemma equiv (e : G ≃* H) (hG : IsFinitelyPresented G) : IsFinitelyPresented H := by
  obtain ⟨n, rels, ⟨f⟩⟩ := hG
  exact ⟨n, rels, ⟨f.trans e⟩⟩

/-- A finitely presented group is finitely generated. -/
lemma fg (hG : IsFinitelyPresented G) : Group.FG G := by
  obtain ⟨n, rels, ⟨e⟩⟩ := hG
  haveI : Group.FG (PresentedGroup (rels : Set (FreeGroup (Fin n)))) :=
    Group.fg_iff.mpr ⟨Set.range PresentedGroup.of, PresentedGroup.closure_range_of _,
      Set.finite_range _⟩
  exact Group.fg_of_surjective (f := e.toMonoidHom) e.surjective

end IsFinitelyPresented

end Group
