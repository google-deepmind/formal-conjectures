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

/-A group G is binary finite if it is periodic and any two elements of G generate a finite subgroup-/
def BinaryFinite (G : Type*) [Group G] : Prop :=
(∀ x : G, IsOfFinOrder x) ∧ (∀ x y : G, (Subgroup.closure ({x, y} : Set G)).carrier.Finite)

/- G is a 2-group if the order of every element is a power of 2-/
def IsTwoGroup (G : Type*) [Group G] : Prop :=
∀ x : G, ∃ n : ℕ, 0 < n ∧ x ^ (2 ^ n) = 1


/-- Kourovka 4.74b: Is every binary-finite 2-group of order greater than 2 non-simple? -/
@[category research open, question, AMS 20]
theorem kourovka_4_74b :
∀ (G : Type*) [Group G],
BinaryFinite G → IsTwoGroup G → ENat.card G > 2 → ¬ IsSimpleGroup G := by sorry



end Kourovka.«4.74b»
