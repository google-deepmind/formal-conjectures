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
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.PresentedGroup

import Mathlib.Tactic

@[expose] public section

namespace Group

/-- A group $G$ is *finitely presented* if it is isomorphic to a group given by a
finite presentation $\langle x_1, \dots, x_n \mid r_1, \dots, r_m \rangle$, i.e. the
quotient of the free group on $n$ generators by the normal closure of a finite set of
relators. -/
def IsFinitelyPresented (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (rels : Finset (FreeGroup (Fin n))),
    Nonempty (PresentedGroup (rels : Set (FreeGroup (Fin n))) ≃* G)

end Group
