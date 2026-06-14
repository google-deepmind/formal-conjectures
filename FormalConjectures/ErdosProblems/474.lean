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
# Erdős Problem 474

*Reference:* [erdosproblems.com/474](https://www.erdosproblems.com/474)

*References:*
- [Er95d] Erdős, P. *Some of my favourite problems which recently have been solved.*
  In Proc. of the Conf. Topology and Measure VII (Wustrow, 1994), p. 64 (1995).
- [Sh88] Shelah, S. *Consistency of positive partition theorems for graphs and models.*
  In Set theory and its applications (1988), pp. 167–193.
- [Va99] Vaughan, J.E. *Open problems in topology II*, problem 7.81 (1999).
-/

open Cardinal
open scoped Cardinal

namespace Erdos474

universe u

/- ### The bracket partition relation -/

/--
`CardinalBracketRamsey2 α β r` asserts the **bracket partition relation**
$\alpha \to [\beta]^2_r$:

For any $r$-coloring of unordered pairs from a set of cardinality $\alpha$, there is
a subset of cardinality $\beta$ on which some color is missing.

The bracket form is weaker than the round-bracket Ramsey property
$\alpha \to (\beta)^2_r$ (which would require a *monochromatic* $\beta$-sized subset);
here we only require that the coloring restricted to the $\beta$-sized subset is not
surjective onto the $r$ colors.

The coloring is given as a symmetric function `f : X → X → Fin r`; the value on a
diagonal `f x x` is irrelevant (we never quantify over diagonal pairs).
-/
def CardinalBracketRamsey2 (α β : Cardinal.{u}) (r : ℕ) : Prop :=
  ∀ (X : Type u), #X = α →
    ∀ (f : X → X → Fin r), (∀ x y, f x y = f y x) →
      ∃ Y : Set X, #Y = β ∧ ∃ c : Fin r, ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → f x y ≠ c

/- ### The main open problem -/

/--
**Erdős Problem 474** ($100 prize).

Under what set-theoretic assumptions is it true that $2^{\aleph_0} \not\to [\aleph_1]^2_3$,
equivalently, that $\mathbb{R}^2$ can be 3-colored so that every uncountable
$A \subseteq \mathbb{R}^2$ has $A^2$ containing a pair of each color?

The currently open *specific* form (asked in [Va99, 7.81]) is whether the negative
relation is consistent assuming $\mathfrak{c} = \aleph_2$.
-/
@[category research open, AMS 3]
theorem erdos_474 :
    answer(sorry) ↔ ¬ CardinalBracketRamsey2 (𝔠) (ℵ_ 1) 3 := by
  sorry

/- ### Known results -/

namespace erdos_474.variants

/--
**Sierpinski–Kurepa (2 colors).** $2^{\aleph_0} \not\to [\aleph_1]^2_2$ holds in ZFC.

For any 2-coloring of pairs from the continuum there is no uncountable subset on which
some color is missed; equivalently (since one of two colors must be missed if the
coloring is not surjective), there is no monochromatic uncountable subset, contradicting
$2^{\aleph_0} \to (\aleph_1)^2_2$. This negative direction is a ZFC theorem due to
Sierpinski and (independently) Kurepa.
-/
@[category research solved, AMS 3]
theorem sierpinski_kurepa : ¬ CardinalBracketRamsey2 (𝔠) (ℵ_ 1) 2 := by
  sorry

/--
**Erdős under CH.** Assuming the Continuum Hypothesis ($\mathfrak{c} = \aleph_1$),
$2^{\aleph_0} \not\to [\aleph_1]^2_3$.

This is Erdős's original positive contribution; the $100 prize was for deciding the
question without assuming CH.
-/
@[category research solved, AMS 3]
theorem erdos_under_ch (hCH : 𝔠 = ℵ_ 1) :
    ¬ CardinalBracketRamsey2 (𝔠) (ℵ_ 1) 3 := by
  sorry

/--
**Shelah [Sh88] consistency.** It is consistent with ZFC (with very large
$\mathfrak{c}$) that $2^{\aleph_0} \to [\aleph_1]^2_3$ holds.

Stated here as the existence of a witnessing setting: Shelah constructs a forcing
extension in which the positive bracket partition relation holds. We express this as
"`CardinalBracketRamsey2 (𝔠) (ℵ_ 1) 3` is consistent" by stating it as a *possible*
property (not provable nor refutable in ZFC). The Lean-side encoding is the
mathematical statement, with the consistency aspect documented above.
-/
@[category research solved, AMS 3]
theorem shelah_consistent : answer(sorry) ↔ CardinalBracketRamsey2 (𝔠) (ℵ_ 1) 3 := by
  sorry

/--
**Specific Vaughan question [Va99, 7.81]** (still open).

Is it consistent with $\mathfrak{c} = \aleph_2$ that $2^{\aleph_0} \not\to [\aleph_1]^2_3$?

This narrows the open question to a specific cardinal arithmetic regime (intermediate
between Erdős's CH case and Shelah's very-large-$\mathfrak{c}$ case).
-/
@[category research open, AMS 3]
theorem vaughan_aleph_two :
    answer(sorry) ↔ (𝔠 = ℵ_ 2 ∧ ¬ CardinalBracketRamsey2 (𝔠) (ℵ_ 1) 3) := by
  sorry

end erdos_474.variants

/- ### Sanity checks -/

/-- **Monotonicity in the color count.** If the bracket relation holds with $r$ colors,
it holds with any $r' \ge r$ colors: more colors only make missing one easier. -/
@[category test, AMS 3]
theorem cardinalBracketRamsey2_mono_colors {α β : Cardinal.{u}} {r r' : ℕ}
    (h : CardinalBracketRamsey2 α β r) (hrr' : r ≤ r') :
    CardinalBracketRamsey2 α β r' := by
  intro X hX f hsym
  -- Compose `f` with the inclusion `Fin r → Fin r'` (via `Fin.castLE`) to reduce to the
  -- `r`-color case. Any `Y` witnessing the `r`-version still misses the same color in
  -- the `r'`-version since the new colors are not in the image.
  sorry

/-- **Monotonicity in the subset size.** If the bracket relation holds for target $\beta$,
it holds for any $\beta' \le \beta$: smaller target is easier. -/
@[category test, AMS 3]
theorem cardinalBracketRamsey2_mono_target {α β β' : Cardinal.{u}} {r : ℕ}
    (h : CardinalBracketRamsey2 α β r) (hβ : β' ≤ β) :
    CardinalBracketRamsey2 α β' r := by
  intro X hX f hsym
  obtain ⟨Y, hY, c, hc⟩ := h X hX f hsym
  obtain ⟨Z, hZsub, hZcard⟩ := (Cardinal.le_mk_iff_exists_subset).mp (hY ▸ hβ)
  exact ⟨Z, hZcard, c, fun x hx y hy hne => hc x (hZsub hx) y (hZsub hy) hne⟩

end Erdos474
