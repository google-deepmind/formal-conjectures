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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 70

**Verbatim statement (Erdős #70, status O):**
> Let $\mathfrak{c}$ be the ordinal of the real numbers, $\beta$ be any countable ordinal, and $2\leq n<\omega$. Is it true that $\mathfrak{c}\to (\beta, n)_2^3$?

**Source:** https://www.erdosproblems.com/70

**Notes:** OPEN


*Reference:* [erdosproblems.com/70](https://www.erdosproblems.com/70)

## Problem Statement

Let 𝔠 be the cardinality of the continuum (i.e. `2 ^ ℵ₀`), let β be any countable ordinal,
and let `2 ≤ n < ω`. Is it true that 𝔠 → (β, n)³₂?

Here the notation 𝔠 → (β, n)³₂ means: for any 2-coloring (red/blue) of all 3-element subsets
of a well-ordered set of order type 𝔠.ord (the smallest ordinal of cardinality 𝔠), either:
- there exists a *red-monochromatic* subset of order type β (every 3-element subset is red), or
- there exists a *blue-monochromatic* subset of cardinality n (every 3-element subset is blue).

This is the 3-uniform (triple) partition relation, as opposed to the 2-uniform (pair/graph)
partition relation `𝔠 → (β, n)²₂` studied in Problems 590–592.

## Known Results

- **Erdős–Rado**: 𝔠 → (ω + n, 4)³₂ for any `2 ≤ n < ω`. In particular, the relation
  𝔠 → (ω + n, 4)³₂ holds for all finite n ≥ 2 (proved; see `erdos_70.variants.erdos_rado`).

## Status

**OPEN**: The general question (arbitrary countable β, finite n ≥ 2) is open.

## Definitions

We introduce `OrdinalCardinalRamsey3 α β c` for the 3-uniform analogue of
`OrdinalCardinalRamsey α β c`: a 2-coloring of 3-element subsets of the ordinal type α
yields either a red set of order type β or a blue set of cardinality c.
-/

open Cardinal Ordinal

namespace Erdos70

universe u

/- ### The 3-uniform partition relation -/

/--
`OrdinalCardinalRamsey3 α β c` asserts the 3-uniform ordinal Ramsey property `α → (β, c)³₂`.

It states that for any 2-coloring of all 3-element subsets of (the ordinal type) `α`,
one of the following must hold:
* There is a red-monochromatic subset of order type β: every 3-element sub-subset is colored
  red. (Formally: a set `s ⊆ α.ToType` with `typeLT s = β` such that any three distinct
  elements of `s` are colored red.)
* There is a blue-monochromatic subset of cardinality `c`: a set `s ⊆ α.ToType` with `#s = c`
  such that every three distinct elements of `s` are colored blue.

The coloring is given as a predicate `isRed : α.ToType → α.ToType → α.ToType → Prop` on
ordered triples of distinct elements; to faithfully encode a coloring of *unordered*
3-element subsets we additionally require `isRed` to be invariant under permutation of
its three (distinct) arguments.
-/
def OrdinalCardinalRamsey3 (α β : Ordinal.{u}) (c : Cardinal.{u}) : Prop :=
  -- For any partition of 3-element subsets into red and blue:
  ∀ (isRed : α.ToType → α.ToType → α.ToType → Prop),
    -- The colouring is well-defined on *unordered* triples of distinct elements:
    (∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (isRed x y z ↔ isRed y x z) ∧ (isRed x y z ↔ isRed x z y)) →
    -- either there is a red-monochromatic subset of order type β
    (∃ s : Set α.ToType, typeLT s = β ∧ s.Triplewise isRed) ∨
    -- or there is a blue-monochromatic subset of cardinality c
    (∃ s : Set α.ToType, #s = c ∧ s.Triplewise (fun x y z ↦ ¬ isRed x y z))

/--
The ordinal of the continuum: the smallest ordinal whose cardinality equals the continuum `𝔠`.
This is `Cardinal.continuum.ord` in Mathlib notation.

Erdős writes "𝔠" for the *ordinal type* of the reals; formally (under AC) this is any ordinal
whose underlying set has cardinality `2 ^ ℵ₀`. The canonical choice is `𝔠.ord`.
-/
noncomputable abbrev continuumOrd : Ordinal.{0} := Cardinal.continuum.ord

/- ### The main open problem -/

/--
**Erdős Problem 70** (Open): Let 𝔠 be the cardinality of the continuum, let β be a countable
ordinal, and let `2 ≤ n < ω`. Is it true that 𝔠 → (β, n)³₂?

Formally: for any countable ordinal β and any natural number n ≥ 2, does
`OrdinalCardinalRamsey3 𝔠.ord β n` hold?

Here:
- `𝔠.ord = Cardinal.continuum.ord` is the least ordinal of cardinality the continuum.
- `β` ranges over countable ordinals (i.e. `β.card ≤ ℵ₀`).
- `n : ℕ` satisfies `2 ≤ n`.
- `OrdinalCardinalRamsey3 α β c` is the 3-uniform partition relation `α → (β, c)³₂`.
-/
@[category research open, AMS 3]
theorem erdos_70 :
    answer(sorry) ↔
    ∀ᵉ (β : Ordinal.{0}) (n : ℕ) (_ : β.card ≤ ℵ₀) (_ : 2 ≤ n),
      OrdinalCardinalRamsey3 continuumOrd β n := by
  sorry

/- ### Variants -/

namespace erdos_70.variants

/--
**Erdős–Rado partial result**: 𝔠 → (ω + n, 4)³₂ for any `2 ≤ n < ω`.

Erdős and Rado proved that any 2-coloring of 3-element subsets of a set of cardinality 𝔠
contains either a red-monochromatic subset of order type ω + n (for any fixed finite n ≥ 2),
or a blue-monochromatic set of cardinality 4.

This gives a positive partial answer to Problem 70 with β = ω + n and the blue side fixed at 4.

**Status**: TRUE (Erdős–Rado).
-/
@[category research solved, AMS 3]
theorem erdos_rado (n : ℕ) (hn : 2 ≤ n) :
    OrdinalCardinalRamsey3 continuumOrd (ω + n) 4 := by
  sorry

/--
**Special case**: 𝔠 → (ω, 3)³₂.

The simplest non-trivial instance of Erdős Problem 70: β = ω (the first infinite countable
ordinal) and n = 3. Does every 2-coloring of 3-element subsets of the continuum contain
either a red-monochromatic set of order type ω (an infinite red-monochromatic subset) or a
blue-monochromatic set of 3 elements (a blue triple)?

**Status**: OPEN (follows from the main conjecture with β = ω, n = 3).
-/
@[category research open, AMS 3]
theorem omega_three :
    answer(True) ↔ OrdinalCardinalRamsey3 continuumOrd ω 3 := by
  sorry

/--
**The relation at ω₁**: 𝔠 → (ω₁, n)³₂ for finite n ≥ 2, where ω₁ = ℵ₁ is the first
uncountable ordinal.

Note that ω₁ is *not* a countable ordinal, so this is not directly an instance of the
main Erdős problem (which asks for *countable* β). However, it is a closely related question.
Under the Continuum Hypothesis (CH), ω₁ = 𝔠.ord, making this a self-referential question
about 𝔠.ord → (𝔠.ord, n)³₂.

**Status**: OPEN.
-/
@[category research open, AMS 3]
theorem omega_one :
    answer(True) ↔
    ∀ᵉ (n : ℕ) (_ : 2 ≤ n),
      OrdinalCardinalRamsey3 continuumOrd (Cardinal.aleph 1).ord n := by
  sorry

/--
**Monotonicity of `OrdinalCardinalRamsey3`** (proved):
If `OrdinalCardinalRamsey3 α β c` holds and `β' ≤ β`, `c' ≤ c`, then
`OrdinalCardinalRamsey3 α β' c'` also holds.

This allows us to deduce weaker partition results from stronger ones.
-/
@[category test, AMS 3]
theorem ordinalCardinalRamsey3_mono {α β β' : Ordinal.{u}} {c c' : Cardinal.{u}}
    (h : OrdinalCardinalRamsey3 α β c) (hβ : β' ≤ β) (hc : c' ≤ c) :
    OrdinalCardinalRamsey3 α β' c' := by
  intro isRed hSym
  obtain (⟨s, hs_type, hs_clique⟩ | ⟨s, hs_card, hs_clique⟩) := h isRed hSym
  · -- Red case: s has type β; find a sub-set of type β' ≤ β
    rw [← Ordinal.type_toType β'] at hβ
    obtain ⟨g⟩ := Ordinal.type_le_iff'.mp (hs_type ▸ hβ)
    let t : Set α.ToType := Set.range (Subtype.val ∘ g)
    refine Or.inl ⟨t, ?_, hs_clique.mono (by rintro x ⟨a, rfl⟩; exact (g a).2)⟩
    -- Show typeLT t = β'
    let emb : (· < · : β'.ToType → β'.ToType → Prop) ↪r (· < · : ↑t → ↑t → Prop) :=
      { toFun := fun a => ⟨(g a).val, a, rfl⟩
        inj' := fun a b heq => g.injective (Subtype.ext (congr_arg (fun x : ↑t => x.val) heq))
        map_rel_iff' := g.map_rel_iff }
    have hsurj : Function.Surjective emb := fun ⟨_, hy⟩ => ⟨hy.choose, Subtype.ext hy.choose_spec⟩
    exact (Ordinal.type_eq.mpr ⟨RelIso.ofSurjective emb hsurj |>.symm⟩).trans
      (Ordinal.type_toType β')
  · -- Blue case: s has cardinality c; find a sub-set of cardinality c' ≤ c
    obtain ⟨t, ht_sub, ht_card⟩ := (Cardinal.le_mk_iff_exists_subset).mp (hs_card ▸ hc)
    exact Or.inr ⟨t, ht_card, hs_clique.mono ht_sub⟩

end erdos_70.variants

end Erdos70
