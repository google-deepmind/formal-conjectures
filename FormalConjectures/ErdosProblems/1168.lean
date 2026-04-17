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
# Erdős Problem 1168

*Reference:* [erdosproblems.com/1168](https://www.erdosproblems.com/1168)

*References for known results:*
- [EHR65] Erdős, Paul and Hajnal, András and Rado, Richard, Partition relations for cardinal
  numbers. Acta Math. Acad. Sci. Hungar. (1965), 93-196.
- [Va99] Vâjâitu, Marius and Vaida, Dragoş, Partition relations for uncountable cardinals
  without the GCH. J. Appl. Anal. (1999) 5(2), 257-267. (Reference 7.80 therein.)

## Problem Statement

Prove that
$$\aleph_{\omega+1} \to (\aleph_{\omega+1}, \underbrace{3, 3, \ldots}_{\aleph_0})^2_{\aleph_0}$$
**without** assuming the generalized continuum hypothesis (GCH).

A problem of Erdős, Hajnal, and Rado. Under GCH the result is known (Erdős–Hajnal–Rado [EHR65]).
The challenge is to prove it in plain ZFC.

## The Partition Relation

The notation $\kappa \to (\kappa, \underbrace{3, 3, \ldots}_{\aleph_0})^2_{\aleph_0}$ means:
for any coloring of unordered pairs from the initial ordinal of $\kappa$ with countably many
colors (indexed by $\mathbb{N}$), one of the following holds:
* **Color 0** (*large monochromatic set*): there exists a subset $S$ of the vertex ordinal
  with $|S| = \kappa$ such that every pair from $S$ receives color 0.
* **Color $n+1$** (for some $n : \mathbb{N}$, *triangle*): there exist three distinct elements
  $x, y, z$ from the vertex ordinal such that all three pairs $\{x,y\}$, $\{x,z\}$, $\{y,z\}$
  receive color $n+1$.

## Formalization Notes

- We work with the **initial ordinal** `(ℵ_ (ω + 1)).ord` of `ℵ_{ω+1}` as the vertex set.
  In Mathlib, `ℵ_ (ω + 1)` is `Cardinal.aleph (Ordinal.omega0 + 1)`.
- **Countably many colors** are represented by `ℕ`, since `#ℕ = ℵ₀`.
- The **GCH** is `∀ o : Ordinal, ℶ_ o = ℵ_ o`
  (notation: `ℶ_` from the `Cardinal` namespace for `Cardinal.beth`).
- Here `ω` in `ℵ_ (ω + 1)` is the ordinal `Ordinal.omega0` (the first infinite ordinal),
  so `ℵ_ (ω + 1)` is indeed `ℵ_{\omega+1}`, the successor cardinal of the singular `ℵ_\omega`.
-/

open Cardinal Ordinal SimpleGraph

namespace Erdos1168

universe u

/-
### The countably-colored cardinal partition relation
-/

/--
`CardinalCountableColorRamsey κ` asserts the partition relation
`κ → (κ, 3, 3, …)²_{ℵ₀}` with countably many colors (indexed by `ℕ`).

More precisely, it is a statement about the initial ordinal `κ.ord` of `κ`:
for any coloring `col : Sym2 κ.ord.ToType → ℕ` of unordered pairs from `κ.ord.ToType`,
one of the following holds:
* **Color 0** (*large monochromatic set*): there exists a set `s ⊆ κ.ord.ToType` with
  `#s = κ` such that every pair from `s` is colored 0 (i.e., `col ⟦(x, y)⟧ = 0`
  for all distinct `x, y ∈ s`).
* **Some positive color** (*triangle*): there exists `n : ℕ` and three distinct elements
  `x y z : κ.ord.ToType` such that all three pairs are colored `n + 1`.

This generalizes `OrdinalMultiColorRamsey` from finitely many colors (using `Fin (k+1)`) to
countably many colors (using `ℕ`), consistent with the `ℵ_0` subscript in the partition notation.
-/
def CardinalCountableColorRamsey (κ : Cardinal.{u}) : Prop :=
  ∀ col : Sym2 κ.ord.ToType → ℕ,
    -- Either color-0 large monochromatic set of cardinality κ ...
    (∃ s : Set κ.ord.ToType,
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → col s(x, y) = 0) ∧
      #s = κ) ∨
    -- ... or a monochromatic triangle in some positive color n+1.
    (∃ (n : ℕ) (x y z : κ.ord.ToType),
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      col s(x, y) = n + 1 ∧
      col s(x, z) = n + 1 ∧
      col s(y, z) = n + 1)

/-
### The main open problem
-/

/--
**OPEN**: Prove that $\aleph_{\omega+1} \to (\aleph_{\omega+1}, 3, 3, \ldots)^2_{\aleph_0}$
without assuming the generalized continuum hypothesis.

In any $\aleph_0$-coloring of the pairs of the complete graph on the initial ordinal
of $\aleph_{\omega+1}$, either:
* there is a monochromatic subset of cardinality $\aleph_{\omega+1}$ in color 0, or
* there is a monochromatic triangle $K_3$ in some positive color.

The result is known under GCH (Erdős–Hajnal–Rado [EHR65]).
The open problem (a problem of Erdős, Hajnal, and Rado) asks for a ZFC proof.

Here `ω` is `Ordinal.omega0` (the first infinite ordinal), so `ℵ_ (ω + 1)` is
the successor cardinal of `ℵ_ω` (i.e., $\aleph_{\omega+1}$).

**Status**: OPEN.
-/
@[category research open, AMS 5]
theorem erdos_1168 : CardinalCountableColorRamsey (ℵ_ (ω + 1)) := by
  sorry

/-
### Variants and known results
-/

namespace erdos_1168.variants

/--
**Generalized Continuum Hypothesis (GCH)**: the axiom asserting that for every ordinal `o`,
the beth cardinal `ℶ_ o` equals the aleph cardinal `ℵ_ o`.

Under GCH, $2^{\aleph_\gamma} = \aleph_{\gamma+1}$ for all ordinals $\gamma$, which makes
the successor cardinal of a singular cardinal more tractable for partition calculus arguments.

This is the hypothesis used in the known proofs of the Erdős–Hajnal–Rado partition result
for $\aleph_{\omega+1}$ (see [EHR65]).
-/
def GCH : Prop := ∀ o : Ordinal.{0}, ℶ_ o = ℵ_ o

/--
**Erdős–Hajnal–Rado theorem under GCH** [EHR65]:
$$\aleph_{\omega+1} \to (\aleph_{\omega+1}, \underbrace{3, 3, \ldots}_{\aleph_0})^2_{\aleph_0}$$
assuming the generalized continuum hypothesis.

Under GCH, the successor cardinal $\aleph_{\omega+1} = 2^{\aleph_\omega}$, which enables the
Erdős–Hajnal–Rado partition calculus arguments for successors of singular cardinals.
The proof uses the fact that under GCH, $\aleph_{\omega+1}$ is a successor of a singular cardinal
of cofinality $\omega$, making the "polarized" and "stepping-up" lemmas of partition calculus
applicable.

**Status**: Proved under GCH by Erdős–Hajnal–Rado [EHR65].
-/
@[category research solved, AMS 5]
theorem under_GCH (hGCH : GCH) : CardinalCountableColorRamsey (ℵ_ (ω + 1)) := by
  sorry

/--
**ℵ_{ω+1} is uncountable**: ℵ_{ω+1} is strictly greater than ℵ₀, confirming it is a
genuinely uncountable vertex-set size for the main conjecture.
-/
@[category test, AMS 5]
example : ℵ₀ < ℵ_ (ω + 1) := by
  rw [← aleph_zero]
  apply aleph_lt_aleph.mpr
  exact omega0_pos.trans_le le_self_add

/--
**ℵ_ω < ℵ_{ω+1}**: the cardinal ℵ_{ω+1} is strictly larger than ℵ_ω, confirming that
ℵ_{ω+1} is indeed the *successor* cardinal of the singular ℵ_ω.
-/
@[category test, AMS 5]
example : ℵ_ ω < ℵ_ (ω + 1) := by
  exact aleph_lt_aleph.mpr (lt_add_one ω)

/--
**GCH implies 2^(ℵ_ω) = ℵ_{ω+1}**: under GCH, the power set of ℵ_ω equals ℵ_{ω+1}.

Formally: if GCH holds then `ℶ_ (ω + 1) = ℵ_ (ω + 1)` and
`ℶ_ (succ ω) = 2 ^ ℶ_ ω` (from the recurrence for beth), so
`2 ^ ℵ_ ω = ℵ_ (ω + 1)` follows by the GCH equalities `ℶ_ ω = ℵ_ ω`.
This is the key arithmetic fact used in the Erdős–Hajnal–Rado [EHR65] proof.
-/
@[category test, AMS 5]
theorem GCH_implies_power_aleph_omega (hGCH : GCH) :
    (2 : Cardinal.{0}) ^ ℵ_ ω = ℵ_ (ω + 1) := by
  have h1 : ℶ_ ω = ℵ_ ω := hGCH ω
  have h2 : ℶ_ (ω + 1) = ℵ_ (ω + 1) := hGCH (ω + 1)
  have h3 : ℶ_ (ω + 1) = 2 ^ ℶ_ ω := by
    rw [show (ω : Ordinal.{0}) + 1 = Order.succ ω from (add_one_eq_succ ω).symm]
    exact beth_succ ω
  have h4 : (2 : Cardinal.{0}) ^ ℵ_ ω = ℶ_ (ω + 1) := by
    rw [h3]; congr 1; exact h1.symm
  exact h4.trans h2

/--
**ℵ_{ω+1} is the successor of ℵ_ω**: a key structural fact used in partition calculus.

This uses the Mathlib theorem `Cardinal.aleph_succ`:
`ℵ_ (Ordinal.succ o) = Order.succ (ℵ_ o)` for all ordinals `o`.
Since `ω + 1 = Ordinal.succ ω`, we get `ℵ_ (ω + 1) = Order.succ (ℵ_ ω)`.
-/
@[category test, AMS 5]
theorem aleph_omega_succ_is_successor : ℵ_ (ω + 1) = Order.succ (ℵ_ ω) := by
  conv_lhs => rw [show (ω : Ordinal) + 1 = Order.succ ω from (add_one_eq_succ ω).symm]
  exact aleph_succ ω

/--
**Monotonicity**: if `CardinalCountableColorRamsey κ` holds and `μ ≤ κ`, then
`CardinalCountableColorRamsey μ` holds. A coloring of `μ.ord`-pairs can be extended
(via the initial segment embedding `μ.ord ↪ κ.ord`) to a coloring of `κ.ord`-pairs.
The `κ`-instance then yields a monochromatic set or triangle in `κ.ord.ToType`; restricting
to the image of `μ.ord.ToType` gives the conclusion for `μ`.

**Status**: Open (the formal reduction requires ordinal embedding machinery).
-/
@[category research open, AMS 5]
theorem mono_kappa {μ κ : Cardinal.{u}} (hle : μ ≤ κ)
    (hκ : CardinalCountableColorRamsey κ) : CardinalCountableColorRamsey μ := by
  sorry

end erdos_1168.variants

end Erdos1168
