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

*Reference:* [erdosproblems.com/70](https://www.erdosproblems.com/70)

The 3-uniform (triple) partition relation $\mathfrak{c} \to (\beta, n)^3_2$
on the ordinal of the real numbers — the triple analogue of `OrdinalCardinalRamsey`
used in Problems 590–592.
-/

open Cardinal Ordinal
open scoped Cardinal

namespace Erdos70

universe u

/- ### The 3-uniform partition relation -/

/--
`OrdinalCardinalRamsey3 α β c` asserts the 3-uniform ordinal Ramsey property
$\alpha \to (\beta, c)^3_2$.

It states that for any 2-coloring of all 3-element subsets of (the ordinal type) $\alpha$,
one of the following must hold:
* There is a red-monochromatic subset of order type $\beta$: every 3-element sub-subset is
  colored red. (Formally: a set $s \subseteq \alpha$ with $\operatorname{typeLT} s = \beta$
  such that any three distinct elements of $s$ are colored red.)
* There is a blue-monochromatic subset of cardinality $c$: a set $s \subseteq \alpha$ with
  $\#s = c$ such that every three distinct elements of $s$ are colored blue.

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

/- ### The main open problem -/

/--
**Erdős Problem 70**: Let $\mathfrak{c}$ be the cardinality of the continuum,
let $\beta$ be a countable ordinal, and let $2 \le n < \omega$.
Is it true that $\mathfrak{c} \to (\beta, n)^3_2$?
-/
@[category research open, AMS 3]
theorem erdos_70 :
    answer(sorry) ↔
    ∀ᵉ (β : Ordinal.{0}) (n : ℕ) (_ : β.card ≤ ℵ₀) (_ : 2 ≤ n),
      OrdinalCardinalRamsey3 (𝔠).ord β n := by
  sorry

/- ### Variants -/

namespace erdos_70.variants

/--
**Erdős–Rado partial result**: $\mathfrak{c} \to (\omega + n, 4)^3_2$ for any
$2 \le n < \omega$. Positive partial answer to Problem 70 with $\beta = \omega + n$
and the blue side fixed at $4$.
-/
@[category research solved, AMS 3]
theorem erdos_rado (n : ℕ) (hn : 2 ≤ n) :
    OrdinalCardinalRamsey3 (𝔠).ord (ω + n) 4 := by
  sorry

/--
**Special case**: $\mathfrak{c} \to (\omega, 3)^3_2$.

The simplest non-trivial instance of Erdős Problem 70: $\beta = \omega$ (the first infinite
countable ordinal) and $n = 3$. Does every 2-coloring of 3-element subsets of the continuum
contain either a red-monochromatic set of order type $\omega$ (an infinite red-monochromatic
subset) or a blue-monochromatic set of $3$ elements (a blue triple)?

Follows from the main conjecture with $\beta = \omega$, $n = 3$.
-/
@[category research open, AMS 3]
theorem omega_three :
    answer(sorry) ↔ OrdinalCardinalRamsey3 (𝔠).ord ω 3 := by
  sorry

/--
**The relation at $\omega_1$**: $\mathfrak{c} \to (\omega_1, n)^3_2$ for finite $n \ge 2$,
where $\omega_1 = \aleph_1$ is the first uncountable ordinal.

Note that $\omega_1$ is *not* a countable ordinal, so this is not directly an instance of the
main Erdős problem (which asks for *countable* $\beta$). Under CH, $\omega_1 = \mathfrak{c}.\mathrm{ord}$,
making this a self-referential question about $\mathfrak{c}.\mathrm{ord} \to
(\mathfrak{c}.\mathrm{ord}, n)^3_2$.
-/
@[category research open, AMS 3]
theorem omega_one :
    answer(sorry) ↔
    ∀ᵉ (n : ℕ) (_ : 2 ≤ n),
      OrdinalCardinalRamsey3 (𝔠).ord (Cardinal.aleph 1).ord n := by
  sorry

/--
**Monotonicity of `OrdinalCardinalRamsey3`**:
If `OrdinalCardinalRamsey3 α β c` holds and $\beta' \le \beta$, $c' \le c$, then
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
