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

public import FormalConjecturesUtil

/-!
# Conjecture 9.65

by Ya. P. Sysak

Is a locally soluble group periodic if it is a product of two periodic subgroups?

*Reference:* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v50)
-/

@[expose] public section

open Pointwise

namespace Kourovka.«9.65»

/--
A group G is locally solvable (locally soluble)
if every finitely generated subgroup H of G is solvable (soluble).
-/
def IsLocallySolvable (G : Type*) [Group G] : Prop :=
  ∀ (H : Subgroup G), Subgroup.FG H → Group.IsSolvable H

/--
A group G is a product of two periodic subgroups H, K
if G = H * K.
-/
def IsProdOfTwoPeriodicSubgroups (G : Type*) [Group G] : Prop :=
  ∃ (H K : Subgroup G), IsMulTorsion H ∧ IsMulTorsion K ∧
    Set.univ = (H : Set G) * (K : Set G)

/--
Is a locally solvable (soluble) group G periodic (torsion)
if it is a product of two periodic (torsion) subgroups?
-/
@[category research open, question, AMS 20]
theorem kourovka_9_65 :
    ∀ (G : Type) [Group G],
      IsLocallySolvable G →
      IsProdOfTwoPeriodicSubgroups G →
      IsMulTorsion G := by
  sorry

end Kourovka.«9.65»
