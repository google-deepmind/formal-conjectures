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
# Conjecture 13.17

by S. Vovsi

*Reference:* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300)
-/

@[expose] public section

namespace Kourovka.«13.17»

/-- A representation of a group G on a vector space V is called a
nil-representation if for every v in V and g in G there exists n such
that v(g − 1)n = 0. -/
def IsNilRepresentation {K G V: Type*} [Field K] [Group G] [AddCommGroup V]
  [Module K V] (ρ : Representation K G V) : Prop :=
    ∀ (v : V) (g : G), ∃ n : Nat, ((ρ g - 1) ^ n) v = 0

/--
Is it true that in zero characteristic every irreducible nil-representation is trivial?
-/
@[category research open, question, AMS 20]
theorem kourovka_13_17 {K G V : Type*} [Field K] [CharZero K] [Group G] [AddCommGroup V]
  [Module K V] (ρ : Representation K G V):
   IsNilRepresentation ρ ∧ ρ.IsIrreducible → ρ.IsTrivial := by
  sorry

end Kourovka.«13.17»
