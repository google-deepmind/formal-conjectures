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
# Conjecture 5.59

by B. Hartley

Let G be a locally finite group which is the product of a p-subgroup and a
q-subgroup, where p and q are distinct primes. Is G a {p,q}-group?

*Reference:* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v50)
-/

@[expose] public section

open Pointwise

namespace Kourovka.«5.59»

/--
A group G is locally finite if every finitely generated subgroup of G is finite.
-/
def IsLocallyFinite (G : Type*) [Group G] : Prop :=
  ∀ (H : Subgroup G), Subgroup.FG H → Finite H

/--
A group G is a product of a p-subgroup H and a q-subgroup K,
where p and q are distinct primes if G = H * K.
-/
def IsProdOfDiffPrimeSubgroup (p : ℕ) (q : ℕ) (G : Type*) [Group G] : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧
    ∃ (H K : Subgroup G),
    IsPGroup p H ∧
    IsPGroup q K ∧
    Set.univ = (H : Set G) * (K : Set G)

/--
A periodic (torsion) group G is a π-group for a set π
if the order of each g ∈ G is divisible only by primes in π.
-/
def IsPiGroup (π : Set ℕ) (G : Type*) [Group G] : Prop :=
  IsMulTorsion G ∧
  (∀ (g : G), ∀ (n : ℕ), Nat.Prime n → n ∣ orderOf g → n ∈ π)

/--
Let G be a locally finite group which is the product of a p-subgroup and a
q-subgroup, where p and q are distinct primes. Is G a {p, q}-group?
G is a {p, q}-group means that G is a π-group with π = {p, q}.
-/
@[category research open, question, AMS 20]
theorem kourovka_5_59 :
    ∀ (p q : ℕ), ∀ (G : Type) [Group G],
      IsLocallyFinite G →
      IsProdOfDiffPrimeSubgroup p q G →
      IsPiGroup {p, q} G := by
  sorry

end Kourovka.«5.59»
