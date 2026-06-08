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

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Sym.Sym2
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Ordinal.Exponential

@[expose] public section

open Cardinal Ordinal

/-!
# Ordinal and cardinal partition relations (binary)

This file consolidates the binary ordinal/cardinal partition relations used in several
Erdős set-theory problems:

* `OrdinalRamsey α β γ`        — `α → (β, γ)²`: 2-coloring of pairs of `α`, finding
  monochromatic subsets of ordinal types `β` (red) or `γ` (blue).
* `OrdinalMultiColorRamsey α β γ k` — `α → (β, γ, …, γ)²_{k+1}`: multicolor partition
  with `k` "small" colors targeting cardinality `γ` and one "large" color targeting
  ordinal type `β`.
* `CardinalCountableColorRamsey κ`  — `κ → (κ, 3, 3, …)²_{ℵ₀}`: countably-colored
  partition relation with a large color-0 class and triangle targets in every other
  color.

These complement `OrdinalCardinalRamsey` (see
`FormalConjecturesForMathlib.SetTheory.Cardinal.SimpleGraph`) which uses a cardinality
target on the blue side instead of an ordinal-type target.
-/

universe u

/--
`OrdinalRamsey α β γ` asserts the ordinal Ramsey property `α → (β, γ)²`.

It states that for any 2-coloring of the complete graph on the ordinal `α`,
one of the following must hold:
* There is a red clique which is order-isomorphic to `β` (a red `K_β`).
* There is a blue clique which is order-isomorphic to `γ` (a blue `K_γ`).
-/
def OrdinalRamsey (α β γ : Ordinal.{u}) : Prop :=
  ∀ red blue : SimpleGraph α.ToType, IsCompl red blue →
    (∃ s, red.IsClique s ∧ typeLT s = β) ∨
    (∃ s, blue.IsClique s ∧ typeLT s = γ)

/--
`OrdinalMultiColorRamsey α β γ k` asserts the multicolor partition relation
`α → (β, γ, γ, …, γ)²_{k+1}` (with `k` copies of `γ`).

For any function `col : Sym2 α.ToType → Fin (k + 1)` assigning one of `k+1` colors
to each pair from `α`, one of the following holds:
* **Color 0**: there is a set `s ⊆ α.ToType` of order type `β` that is monochromatic
  in color 0.
* **Color `i+1`** (for some `i : Fin k`): there is a set `s ⊆ α.ToType` with `#s = γ`
  that is monochromatic in color `i.succ`.

When `k = 1` this reduces to the binary partition relation `α → (β, γ)²` on the
cardinality side.
-/
def OrdinalMultiColorRamsey (α β : Ordinal.{u}) (γ : Cardinal.{u}) (k : ℕ) : Prop :=
  ∀ col : Sym2 α.ToType → Fin (k + 1),
    (∃ s : Set α.ToType,
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → col s(x, y) = 0) ∧
      typeLT s = β) ∨
    (∃ (i : Fin k) (s : Set α.ToType),
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → col s(x, y) = i.succ) ∧
      #s = γ)

/--
`CardinalCountableColorRamsey κ` asserts the partition relation
`κ → (κ, 3, 3, …)²_{ℵ₀}` with countably many colors (indexed by `ℕ`).

For any coloring `col : Sym2 κ.ord.ToType → ℕ` of pairs from the initial ordinal of `κ`,
one of the following holds:
* **Color 0** (*large monochromatic set*): there is a set `s ⊆ κ.ord.ToType` with
  `#s = κ` such that every pair in `s` gets color 0.
* **Some positive color** (*triangle*): there are `n : ℕ` and three distinct elements
  `x y z : κ.ord.ToType` such that all three pairs are colored `n + 1`.

This is the countably-colored analogue of `OrdinalMultiColorRamsey`, replacing
`Fin (k+1)` with `ℕ` (so `ℵ_0`-many colors) and requiring monochromatic *triangles*
(rather than arbitrary monochromatic cliques) in the positive colors.
-/
def CardinalCountableColorRamsey (κ : Cardinal.{u}) : Prop :=
  ∀ col : Sym2 κ.ord.ToType → ℕ,
    (∃ s : Set κ.ord.ToType,
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → col s(x, y) = 0) ∧
      #s = κ) ∨
    (∃ (n : ℕ) (x y z : κ.ord.ToType),
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      col s(x, y) = n + 1 ∧
      col s(x, z) = n + 1 ∧
      col s(y, z) = n + 1)
