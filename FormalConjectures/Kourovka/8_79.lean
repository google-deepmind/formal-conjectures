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
# Conjecture 8.79.

by B. Hartley

*Reference:* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v46)
-/

@[expose] public section

namespace Kourovka.«8.79»

/--
A group is locally finite if all finitely generated subgroups
are finite
-/
def IsLocallyFiniteGroup (G : Type*) [Group G] : Prop :=
  ∀ (H : Subgroup G), H.FG → Finite H

/--
An automorphism is inner if it is a conjugation of all *x ∈ G* by some *g ∈ G*
-/
def IsInnerAutomorphism (G : Type*) [Group G] (φ : G ≃* G) : Prop :=
  ∃ (g : G), ∀ (x : G), φ x = g * x  * g⁻¹

/--
The notion of a group having no outer automorphism is equivalent
to every automorphism being inner.
-/
def NoOuterAutomorph (G : Type*) [Group G] : Prop :=
  ∀ φ : G ≃* G, IsInnerAutomorphism G φ

/--
A group is complete if it has no outer automorphisms
and a trivial center.
-/
def IsCompleteGroup (G : Type*) [Group G] : Prop :=
  Subgroup.center G = ⊥ ∧ NoOuterAutomorph G

/--
Does there exist a countable infinite locally finite group that is complete,
in the sense that it has trivial centre and no outer automorphisms?.

The answer is "Yes", if one assumes that the group is uncountable. See
[K.K. Hickin, Trans. Amer. Math. Soc., 239 (1978), 213-227].

-/
@[category research open, question, AMS 20]
theorem Kourovka_8_79 :
   ∃ (G : Type) (_ : Group G), Countable G ∧ Infinite G ∧
   IsLocallyFiniteGroup G ∧ IsCompleteGroup G := by
  sorry

end Kourovka.«8.79»
