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
# Conjecture 4.74(b)


*Reference:* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300)
-/

@[expose] public section

namespace Kourovka.«4.74b»

/-- A group G is N-finite if for any subset of the underlying set of G the generated subgroup is finite. -/
def NFinite (G : Type*) [Group G] (N : ℕ): Prop :=
  ∀ (S : Finset G), S.card ≤ N → (Subgroup.closure (S : Set G)).carrier.Finite

/-- Kourovka 4.74b: Is every binary-finite 2-group of order greater than 2 non-simple? -/
@[category research open, question, AMS 20]
theorem kourovka_4_74b :
  ∀ (G : Type*) [Group G],
    NFinite G 2 → IsPGroup 2 G → ENat.card G > 2 → ¬ IsSimpleGroup G := by sorry

end Kourovka.«4.74b»
