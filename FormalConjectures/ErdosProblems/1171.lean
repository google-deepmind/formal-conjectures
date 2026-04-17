/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 1171

*Reference:* [erdosproblems.com/1171](https://www.erdosproblems.com/1171)

*References for known results:*
- [EH74] Erdős, Paul and Hajnal, András, Unsolved and solved problems in set theory. Proceedings
  of the Tarski symposium (1974), 269-287.
- [Ba89b] Baumgartner, James E., Partition relations for countable topological spaces. J. Combin.
  Theory Ser. A (1986), 38-54.

## Problem Statement

Is it true that, for all finite $k$ (with $k < \omega$),
$$\omega_1^2 \to (\omega_1 \cdot \omega, \underbrace{3, \ldots, 3}_{k})^2_{k+1}?$$

This is a multicolor generalization of the Erdős–Hajnal theorem. It asks whether every
$(k+1)$-coloring of the pairs (edges) of the complete graph on $\omega_1^2$ either:
- produces a monochromatic set of order type $\omega_1 \cdot \omega$ in color 0, or
- produces a monochromatic triangle $K_3$ in some non-zero color $i \in \{1, \ldots, k\}$.

## Known Results

- **Erdős–Hajnal** [EH74]: $\omega_1^2 \to (\omega_1 \cdot \omega, 3)^2$ (the $k = 1$ case).
  This is the binary partition relation with one "large" color and one "triangle" color.
- **Baumgartner** [Ba89b]: Under a form of Martin's axiom (MA), the binary relation
  $\omega_1 \cdot \omega \to (\omega_1 \cdot \omega, 3)^2$ holds.

## Overview

The key novelty here is `OrdinalMultiColorRamsey`: a $(k+1)$-color generalization of the
binary ordinal Ramsey relation. In `OrdinalMultiColorRamsey α β γ k`:
- `α` is the ordinal whose pairs are colored (the vertex set),
- `β` is the ordinal type required for a color-0 clique,
- `γ` is the clique size (as a cardinal) required for each non-zero color,
- `k` is the number of non-zero colors (so there are `k+1` colors total).

The open question `erdos_1171` asks whether this holds for all finite `k` with
`α = ω₁²`, `β = ω₁ · ω`, `γ = 3`.
-/

open Cardinal Ordinal SimpleGraph

namespace Erdos1171

universe u

/- ### The multicolor ordinal partition relation -/

/--
`OrdinalMultiColorRamsey α β γ k` asserts the multicolor partition relation
`α → (β, γ, γ, …, γ)²_{k+1}` (with `k` copies of `γ`).

It states: for any function `col : Sym2 α.ToType → Fin (k + 1)` assigning one of `k+1` colors
to each pair from `α`, one of the following holds:
* Color 0: there is a set `s ⊆ α.ToType` of order type `β` that is monochromatic in color 0
  (i.e. every pair in `s` gets color 0), or
* Color i (for some `i : Fin k`): there is a set `s ⊆ α.ToType` with `#s = γ` that is
  monochromatic in color `i.succ` (i.e. every pair in `s` gets color `i.succ`).

When `k = 1` this reduces to the binary partition relation `α → (β, γ)²`.
-/
def OrdinalMultiColorRamsey (α β : Ordinal.{u}) (γ : Cardinal.{u}) (k : ℕ) : Prop :=
  ∀ col : Sym2 α.ToType → Fin (k + 1),
    -- Either color-0 clique of order type β ...
    (∃ s : Set α.ToType,
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → col s(x, y) = 0) ∧
      typeLT s = β) ∨
    -- ... or for some non-zero color i, a clique of cardinality γ.
    (∃ (i : Fin k) (s : Set α.ToType),
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → col s(x, y) = i.succ) ∧
      #s = γ)

/- ### The main open problem -/

/--
**OPEN**: Is it true that for all finite $k < \omega$,
$$\omega_1^2 \to (\omega_1 \cdot \omega, \underbrace{3, \ldots, 3}_{k})^2_{k+1}?$$

In any $(k+1)$-coloring of the pairs of the complete graph on $\omega_1^2$, either:
* there is a color-0 set of order type $\omega_1 \cdot \omega$, or
* there is a monochromatic triangle $K_3$ in some non-zero color.

The case $k = 1$ (binary, `erdos_1171.variants.k_one`) is the Erdős–Hajnal theorem.

**Status**: OPEN.
-/
@[category research open, AMS 5]
theorem erdos_1171 : ∀ k : ℕ, OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k := by
  sorry

/- ### Variants and known results -/

namespace erdos_1171.variants

/--
**Erdős–Hajnal theorem**: The case $k = 1$.

$\omega_1^2 \to (\omega_1 \cdot \omega, 3)^2$: in any 2-coloring of the pairs of $K_{\omega_1^2}$,
there is either a color-0 set of order type $\omega_1 \cdot \omega$, or a color-1 triangle.

This is the binary Ramsey relation `OrdinalRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3`, which can be
seen as the $k = 1$ instance of `OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 1`.

**Status**: Proved (Erdős–Hajnal [EH74]).
-/
@[category research solved, AMS 5]
theorem k_one : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 1 := by
  sorry

/--
**Reduction**: `OrdinalMultiColorRamsey` is monotone in the number of non-zero colors.

If the `k`-color version `OrdinalMultiColorRamsey α β γ k` holds, then the `j`-color version
holds for all `j ≤ k`. A `j+1`-coloring can be embedded into a `k+1`-coloring by composing
with the inclusion `Fin (j+1) ↪ Fin (k+1)`, so a witness for the `k`-color version
provides a witness for the `j`-color version.
-/
@[category research solved, AMS 5]
theorem mono_k {j k : ℕ} (hjk : j ≤ k)
    (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j := by
  sorry

/--
**Baumgartner under MA**: Assuming a form of Martin's Axiom, the binary partition relation
$\omega_1 \cdot \omega \to (\omega_1 \cdot \omega, 3)^2$ holds.

Baumgartner [Ba89b] proved that under MA(countable), the order type $\omega_1 \cdot \omega$
itself has the self-similar Ramsey property with triangles. This is the $k = 1$ case
with $\alpha = \omega_1 \cdot \omega$ (rather than $\omega_1^2$).

This provides evidence toward `erdos_1171` by establishing a Ramsey-type property at
the "target" order type.

**Status**: Proved under MA(countable) by Baumgartner [Ba89b].
-/
@[category research solved, AMS 5]
theorem baumgartner_under_MA :
    -- MA(countable) placeholder: in this formalization we take it as a hypothesis.
    -- The actual statement of MA(countable) involves a forcing axiom for c.c.c. posets.
    True →
    OrdinalMultiColorRamsey (ω_ 1 * ω) (ω_ 1 * ω) 3 1 := by
  intro _hMA
  sorry

end erdos_1171.variants

end Erdos1171
