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
# Conjecture 6.48


*Reference:* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300)
-/

@[expose] public section

namespace Kourovka.«6.48»

/-A group G is binary finite if it is periodic and any two elements of G generate a finite subgroup-/
def BinaryFinite (G : Type*) [Group G] : Prop :=
(∀ x : G, IsOfFinOrder x) ∧ (∀ x y : G, Set.Finite {z : G | ∃ a b : ℤ, z = x ^ a * y ^ b})

/- G is a p-group if the order of every element is a power of p-/
def IsPGroup (G : Type*) [Group G] (p : ℕ): Prop :=
∀ x : G, ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) = 1

/-- Kourovka 6.48: Is every infinite binary finite p-group non-simple? Here p is a prime number -/
@[category research open, question, AMS 20]
theorem kourovka_6_48 :
∀ (G : Type*) [Group G] [Infinite G], ∀ p : ℕ, Nat.Prime p → BinaryFinite G → IsPGroup G p → ¬ IsSimpleGroup G := by sorry


end Kourovka.«6.48»
