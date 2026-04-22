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
# Erdős Problem 1172

**Verbatim statement (Erdős #1172, status O):**
> Establish whether the following are true assuming the generalised continuum hypothesis:\[\omega_3 \to (\omega_2,\omega_1+2)^2,\]\[\omega_3\to (\omega_2+\omega_1,\omega_2+\omega)^2,\]\[\omega_2\to (\omega_1^{\omega+2}+2, \omega_1+2)^2.\]Establish whether the following is consistent with the generalised continuum hypothesis:\[\omega_2\to (\omega_1+\omega)_2^2,\]or even $\omega_2 \to (\xi)_2^2$ for all $\xi<\omega_2$.

**Source:** https://www.erdosproblems.com/1172

**Notes:** OPEN


*Reference:* [erdosproblems.com/1172](https://www.erdosproblems.com/1172)

*References for known results:*
- [EH74] Erdős, Paul and Hajnal, András, Unsolved and solved problems in set theory.
  Proceedings of the Tarski symposium (1974), 269–287.
- [ER56] Erdős, Paul and Rado, Richard, A partition calculus in set theory.
  Bull. Amer. Math. Soc. (1956), 427–489.

## Problem Statement

A problem of Erdős and Hajnal. The following four partition relations are open (each under the
indicated set-theoretic hypothesis):

1. Under GCH: $\omega_3 \to (\omega_2, \omega_1 + 2)^2$
2. Under GCH: $\omega_3 \to (\omega_2 + \omega_1, \omega_2 + \omega)^2$
3. Under GCH: $\omega_2 \to (\omega_1^{\omega+2} + 2, \omega_1 + 2)^2$
4. Under CH:  $\omega_2 \to (\omega_1 + \omega)^2_2$

Here `ω_ n` denotes the `n`-th uncountable limit ordinal (= `Ordinal.omega n` in Mathlib),
so `ω_ 1` is the first uncountable ordinal, `ω_ 2` the second, and `ω_ 3` the third.

The problem is related to the **Erdős–Rado partition theorem** [ER56]:
$(2^\kappa)^+ \to (\kappa^+ + 1)^2_\kappa$ for every infinite cardinal $\kappa$.

**Status**: OPEN.

## Formalization notes

- `OrdinalRamsey α β γ` (from `FormalConjecturesForMathlib`) encodes `α → (β, γ)²`:
  any 2-coloring of the complete graph on ordinal `α` yields a red clique of order type `β`
  or a blue clique of order type `γ`.
- GCH is encoded as a `Prop` asserting `2 ^ ℵ_ o = ℵ_ (Order.succ o)` for every ordinal `o`
  (equivalently, `ℶ_ o = ℵ_ o` for all `o`). Mathlib has no built-in GCH axiom; it is passed
  as a hypothesis. The formulation follows the convention in `Erdos1173`.
- CH (Continuum Hypothesis) is `2 ^ ℵ₀ = ℵ_ 1`; it is a special case of GCH.
- The subscript `2` in part (4), $\omega_2 \to (\omega_1 + \omega)^2_2$, indicates 2 colors.
  Since `OrdinalRamsey` already uses a 2-coloring, part (4) becomes the symmetric relation
  `OrdinalRamsey (ω_ 2) (ω_ 1 + ω) (ω_ 1 + ω)`.
-/

open Cardinal Ordinal

namespace Erdos1172

/- ### Local definition of `OrdinalRamsey` -/

/--
`OrdinalRamsey α β γ` asserts the ordinal Ramsey property `α → (β, γ)²`.

It states that for any 2-coloring of the complete graph on the ordinal `α`,
one of the following must hold:
* There is a red clique which is order-isomorphic to `β` (a red `K_β`).
* There is a blue clique which is order-isomorphic to `γ` (a blue `K_γ`).
-/
def OrdinalRamsey (α β γ : Ordinal) : Prop :=
  ∀ red blue : SimpleGraph α.ToType, IsCompl red blue →
    (∃ s, red.IsClique s ∧ typeLT s = β) ∨
    (∃ s, blue.IsClique s ∧ typeLT s = γ)

/- ### Hypotheses: GCH and CH -/

/--
The **Generalized Continuum Hypothesis (GCH)**: for every ordinal `o`,
$2^{\aleph_o} = \aleph_{o+1}$.

This is independent of ZFC. We encode it as a `Prop` following the convention in `Erdos1173`:
`∀ o : Ordinal.{0}, (2 : Cardinal.{0}) ^ ℵ_ o = ℵ_ (Order.succ o)`.
-/
def GCH : Prop := ∀ o : Ordinal.{0}, (2 : Cardinal.{0}) ^ ℵ_ o = ℵ_ (Order.succ o)

/--
The **Continuum Hypothesis (CH)**: $2^{\aleph_0} = \aleph_1$.

This is the special case `o = 0` of GCH, since `ℵ_ (Order.succ 0) = ℵ_ 1`.
-/
def CH : Prop := (2 : Cardinal.{0}) ^ ℵ₀ = ℵ_ 1

/-- GCH implies CH: apply GCH at `o = 0` and use `ℵ_ (Order.succ 0) = ℵ_ 1`. -/
@[category undergraduate, AMS 5]
theorem gch_implies_ch (h : GCH) : CH := by
  unfold GCH at h
  unfold CH
  have h0 := h 0
  simp [Cardinal.aleph_zero, Ordinal.succ_zero] at h0
  exact h0

/- ### The main open problems -/

/--
**Erdős–Hajnal Problem 1172, Part 1**: Under GCH,
$$\omega_3 \to (\omega_2, \omega_1 + 2)^2.$$

Every 2-coloring of the complete graph on $\omega_3$ either contains a red clique of order type
$\omega_2$ or a blue clique of order type $\omega_1 + 2$.

**Status**: OPEN.
-/
@[category research open, AMS 5]
theorem erdos_1172.part1 (hGCH : GCH) :
    OrdinalRamsey (ω_ 3) (ω_ 2) (ω_ 1 + 2) := by
  sorry

/--
**Erdős–Hajnal Problem 1172, Part 2**: Under GCH,
$$\omega_3 \to (\omega_2 + \omega_1, \omega_2 + \omega)^2.$$

Every 2-coloring of the complete graph on $\omega_3$ either contains a red clique of order type
$\omega_2 + \omega_1$ or a blue clique of order type $\omega_2 + \omega$.

**Status**: OPEN.
-/
@[category research open, AMS 5]
theorem erdos_1172.part2 (hGCH : GCH) :
    OrdinalRamsey (ω_ 3) (ω_ 2 + ω_ 1) (ω_ 2 + ω) := by
  sorry

/--
**Erdős–Hajnal Problem 1172, Part 3**: Under GCH,
$$\omega_2 \to (\omega_1^{\omega+2} + 2, \omega_1 + 2)^2.$$

Every 2-coloring of the complete graph on $\omega_2$ either contains a red clique of order type
$\omega_1^{\omega+2} + 2$ or a blue clique of order type $\omega_1 + 2$.

Here `ω_ 1 ^ (ω + 2)` is ordinal exponentiation: $\omega_1^{\omega + 2}$.

**Status**: OPEN.
-/
@[category research open, AMS 5]
theorem erdos_1172.part3 (hGCH : GCH) :
    OrdinalRamsey (ω_ 2) (ω_ 1 ^ (ω + 2) + 2) (ω_ 1 + 2) := by
  sorry

/--
**Erdős–Hajnal Problem 1172, Part 4**: Under CH,
$$\omega_2 \to (\omega_1 + \omega)^2_2.$$

Every 2-coloring of the complete graph on $\omega_2$ contains a monochromatic set of order
type $\omega_1 + \omega$ in some color. The subscript $2$ denotes 2 colors; since `OrdinalRamsey`
uses a 2-coloring, this is the symmetric relation
`OrdinalRamsey (ω_ 2) (ω_ 1 + ω) (ω_ 1 + ω)`.

**Status**: OPEN.
-/
@[category research open, AMS 5]
theorem erdos_1172.part4 (hCH : CH) :
    OrdinalRamsey (ω_ 2) (ω_ 1 + ω) (ω_ 1 + ω) := by
  sorry

/--
**Erdős–Hajnal Problem 1172** (combined statement): All four open partition relations hold
under the appropriate hypotheses (GCH for parts 1–3, CH for part 4).

A positive answer would significantly extend the Erdős–Rado theorem
$(2^\kappa)^+ \to (\kappa^+ + 1)^2_\kappa$ in the direction of uncountable ordinal partition
calculus under GCH.

**Status**: OPEN.
-/
@[category research open, AMS 5]
theorem erdos_1172 (hGCH : GCH) :
    OrdinalRamsey (ω_ 3) (ω_ 2) (ω_ 1 + 2) ∧
    OrdinalRamsey (ω_ 3) (ω_ 2 + ω_ 1) (ω_ 2 + ω) ∧
    OrdinalRamsey (ω_ 2) (ω_ 1 ^ (ω + 2) + 2) (ω_ 1 + 2) ∧
    OrdinalRamsey (ω_ 2) (ω_ 1 + ω) (ω_ 1 + ω) := by
  sorry

/- ### Related known result: Erdős–Rado theorem -/

/--
**Erdős–Rado partition theorem** [ER56]: $(2^\kappa)^+ \to (\kappa^+ + 1)^2_\kappa$.

For every infinite cardinal $\kappa$, any $\kappa$-coloring of the 2-element subsets of a
set of cardinality $(2^\kappa)^+$ has a monochromatic set of cardinality $\kappa^+ + 1$.

Under GCH, $2^{\aleph_n} = \aleph_{n+1}$ for all finite $n$. In particular, GCH gives
$\omega_2 = (2^{\aleph_0})^+$ and the Erdős–Rado theorem then gives $\omega_2 \to (\omega_1 + 1)^2$,
meaning any 2-coloring of $K_{\omega_2}$ has a red or blue clique of order type $\omega_1 + 1$.
The statements in Problem 1172 seek larger homogeneous sets (e.g., $\omega_1 + 2$ or
$\omega_1^{\omega+2} + 2$) and represent open extensions of this theorem.

**Status**: TRUE (Erdős–Rado [ER56]).
-/
@[category research solved, AMS 5]
theorem erdos_rado_binary_instance (hGCH : GCH) :
    OrdinalRamsey (ω_ 2) (ω_ 1 + 1) (ω_ 1 + 1) := by
  -- Under GCH, 2^ℵ₀ = ℵ₁ so (2^ℵ₀)⁺ = ℵ₂, realized as ordinal ω_2.
  -- Erdős–Rado gives any 2-coloring of K_{ω_2} has a monochromatic clique of card ℵ₁ = ω_1,
  -- i.e., order type ≥ ω_1 + 1.  The full proof uses the Erdős–Rado theorem for κ = ℵ₀.
  sorry

/- ### Sanity checks -/

/-- `ω_ 1 < ω_ 2 < ω_ 3`: the uncountable limit ordinals are strictly increasing. -/
@[category test, AMS 5]
example : ω_ 1 < ω_ 2 ∧ ω_ 2 < ω_ 3 := by
  exact ⟨Ordinal.omega_lt_omega.mpr one_lt_two,
         Ordinal.omega_lt_omega.mpr (by norm_num)⟩

/-- GCH implies CH. -/
@[category test, AMS 5]
example (h : GCH) : CH := gch_implies_ch h

/--
The blue target `ω_ 1 + 2` in Part 1 is strictly less than `ω_ 2`.
Since `ω_ 2` is a principal ordinal under addition (`Principal (· + ·) (ω_ 2)`),
any two ordinals below `ω_ 2` have their sum below `ω_ 2`.
-/
@[category test, AMS 5]
example : ω_ 1 + 2 < ω_ 2 := by
  apply principal_add_omega
  · exact Ordinal.omega_lt_omega.mpr one_lt_two
  · -- 2 < ω_ 2: since 2 < ω ≤ ω_ 2
    calc (2 : Ordinal) < ω := by exact_mod_cast Ordinal.nat_lt_omega0 2
      _ ≤ ω_ 2 := omega0_le_omega 2

/-- The ordinal `ω_ 1 ^ (ω + 2)` appearing in Part 3 is positive. -/
@[category test, AMS 5]
example : 0 < ω_ 1 ^ (ω + 2) := Ordinal.opow_pos _ (Ordinal.omega_pos 1)

end Erdos1172
