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
public import FormalConjecturesForMathlib.SetTheory.Cardinal.SimpleGraph

@[expose] public section

open Cardinal Ordinal

/-!
# Ordinal and cardinal partition relations (binary)

This file consolidates the binary ordinal/cardinal partition relations used in several
Erdős set-theory problems:

* `OrdinalRamsey α β γ` — `α → (β, γ)²`: 2-coloring of pairs of `α`, finding
  monochromatic subsets of ordinal types `β` (red) or `γ` (blue).
* `OrdinalMultiColorRamsey α β γ k` — `α → (β, γ, …, γ)²_{k+1}`: multicolor partition
  with `k` "small" colors targeting cardinality `γ` and one "large" color targeting
  ordinal type `β`.
* `CardinalCountableColorRamsey κ` — `κ → (κ, 3, 3, …)²_{ℵ₀}`: countably-colored
  partition relation with a large color-0 class and triangle targets in every other
  color.

These complement `OrdinalCardinalRamsey` (see
`FormalConjecturesForMathlib.SetTheory.Cardinal.SimpleGraph`) which uses a cardinality
target on the blue side instead of an ordinal-type target; the bridge lemma
`ordinalMultiColorRamsey_one_iff_ordinalCardinalRamsey` identifies the `k = 1` case of
the `Sym2`-coloring style with that `SimpleGraph`-pair style.
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
* **Color 0**: there is a set `A ⊆ α.ToType` of order type `β` that is monochromatic
  in color 0.
* **Color `i+1`** (for some `i : Fin k`): there is a set `A ⊆ α.ToType` with `#A = γ`
  that is monochromatic in color `i.succ`.

When `k = 1` this reduces to the binary partition relation `α → (β, γ)²` on the
cardinality side (see `ordinalMultiColorRamsey_one_iff_ordinalCardinalRamsey`).
-/
def OrdinalMultiColorRamsey (α β : Ordinal.{u}) (γ : Cardinal.{u}) (k : ℕ) : Prop :=
  ∀ col : Sym2 α.ToType → Fin (k + 1),
    (∃ A : Set α.ToType,
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → col s(x, y) = 0) ∧
      typeLT A = β) ∨
    (∃ (i : Fin k) (A : Set α.ToType),
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → col s(x, y) = i.succ) ∧
      #A = γ)

/--
`CardinalCountableColorRamsey κ` asserts the partition relation
`κ → (κ, 3, 3, …)²_{ℵ₀}` with countably many colors (indexed by `ℕ`).

For any coloring `col : Sym2 κ.ord.ToType → ℕ` of pairs from the initial ordinal of `κ`,
one of the following holds:
* **Color 0** (*large monochromatic set*): there is a set `A ⊆ κ.ord.ToType` with
  `#A = κ` such that every pair in `A` gets color 0.
* **Some positive color** (*triangle*): there are `n : ℕ` and three distinct elements
  `x y z : κ.ord.ToType` such that all three pairs are colored `n + 1`.

This is the countably-colored analogue of `OrdinalMultiColorRamsey`, replacing
`Fin (k+1)` with `ℕ` (so `ℵ_0`-many colors) and requiring monochromatic *triangles*
(rather than arbitrary monochromatic cliques) in the positive colors.
-/
def CardinalCountableColorRamsey (κ : Cardinal.{u}) : Prop :=
  ∀ col : Sym2 κ.ord.ToType → ℕ,
    (∃ A : Set κ.ord.ToType,
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → col s(x, y) = 0) ∧
      #A = κ) ∨
    (∃ (n : ℕ) (x y z : κ.ord.ToType),
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      col s(x, y) = n + 1 ∧
      col s(x, z) = n + 1 ∧
      col s(y, z) = n + 1)

/--
**Bridge between the two coloring styles.** For `k = 1`, the `Sym2`-coloring relation
`OrdinalMultiColorRamsey α β γ 1` coincides with the `SimpleGraph`-style relation
`OrdinalCardinalRamsey α β γ` (a complementary pair of graphs, with an order-type
target `β` on the red side and a cardinality target `γ` on the blue side).
-/
theorem ordinalMultiColorRamsey_one_iff_ordinalCardinalRamsey
    (α β : Ordinal.{u}) (γ : Cardinal.{u}) :
    OrdinalMultiColorRamsey α β γ 1 ↔ OrdinalCardinalRamsey α β γ := by
  classical
  constructor
  · intro h red blue hcompl
    -- Color a pair with `0` when it is a red edge, `1` otherwise.
    obtain ⟨A, hmono, htype⟩ | ⟨i, A, hmono, hcard⟩ :=
      h (Sym2.lift ⟨fun x y => if red.Adj x y then 0 else 1, fun x y => by
        simp [SimpleGraph.adj_comm]⟩)
    · refine Or.inl ⟨A, fun x hx y hy hne => ?_, htype⟩
      have hcol := hmono x hx y hy hne
      simp only [Sym2.lift_mk] at hcol
      by_contra hadj
      rw [if_neg hadj] at hcol
      exact absurd hcol (by decide)
    · obtain rfl : i = 0 := Subsingleton.elim i 0
      refine Or.inr ⟨A, fun x hx y hy hne => ?_, hcard⟩
      have hcol := hmono x hx y hy hne
      simp only [Sym2.lift_mk] at hcol
      have hnred : ¬ red.Adj x y := by
        intro hadj
        rw [if_pos hadj] at hcol
        exact absurd hcol (by decide)
      have hsup : (red ⊔ blue).Adj x y := by
        rw [hcompl.sup_eq_top]
        simpa using hne
      exact ((SimpleGraph.sup_adj red blue x y).mp hsup).resolve_left hnred
  · intro h col
    -- Turn the coloring into the graph of `0`-colored pairs and its complement.
    let red : SimpleGraph α.ToType :=
      { Adj := fun x y => x ≠ y ∧ col s(x, y) = 0
        symm := fun x y hxy => ⟨hxy.1.symm, by rw [Sym2.eq_swap]; exact hxy.2⟩
        loopless := fun x hx => hx.1 rfl }
    obtain ⟨A, hclique, htype⟩ | ⟨A, hclique, hcard⟩ := h red redᶜ isCompl_compl
    · exact Or.inl ⟨A, fun x hx y hy hne => (hclique hx hy hne).2, htype⟩
    · refine Or.inr ⟨0, A, fun x hx y hy hne => ?_, hcard⟩
      have hadj := hclique hx hy hne
      rw [SimpleGraph.compl_adj] at hadj
      have hne0 : col s(x, y) ≠ 0 := fun h0 => hadj.2 ⟨hne, h0⟩
      have key : ∀ c : Fin 2, c ≠ 0 → c = 1 := by decide
      rw [key _ hne0, Fin.succ_zero_eq_one]
