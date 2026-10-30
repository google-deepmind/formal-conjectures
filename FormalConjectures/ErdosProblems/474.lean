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
# Erdős Problem 474

*References:*
- [erdosproblems.com/474](https://www.erdosproblems.com/474)
- [Er95d] Erdős, P. *On some problems in combinatorial set theory.*
  Publ. Inst. Math. 57(71) (1995), 61–65.
- [Sh88] Shelah, S. *Was Sierpiński right? I.* Israel J. Math. 62 (1988), 355–380.
- [Va99] Various, *Some of Paul’s favorite problems*, Budapest conference booklet,
  problem 7.81 (1999).
-/

@[expose] public section

open Cardinal Combinatorics
open scoped Cardinal

namespace Erdos474

universe u

/- ### The main open problem -/

/--
**Erdős Problem 474** ($100 prize).

Under what set-theoretic assumptions is it true that $2^{\aleph_0} \not\to [\aleph_1]^2_3$,
equivalently, that $\mathbb{R}^2$ can be 3-colored so that every uncountable
$A \subseteq \mathbb{R}^2$ has $A^2$ containing a pair of each color?

The currently open *specific* form (asked in [Va99, 7.81]) is whether the negative
relation is consistent assuming $\mathfrak{c} = \aleph_2$.
-/
@[category research open, question, AMS 3]
theorem erdos_474 :
    ¬ cardinalBracketRamsey2 (𝔠) (ℵ_ 1) 3 := by
  sorry

/- ### Known results -/

namespace erdos_474.variants

/--
**Sierpinski–Kurepa (2 colors).** $2^{\aleph_0} \not\to [\aleph_1]^2_2$ holds in ZFC.

There exists a 2-coloring of pairs from the continuum with no uncountable monochromatic
subset. Equivalently, every uncountable subset contains a pair of each colour.
-/
@[category research solved, AMS 3]
theorem sierpinski_kurepa : ¬ cardinalBracketRamsey2 (𝔠) (ℵ_ 1) 2 := by
  sorry

/--
**Erdős under CH.** Assuming the Continuum Hypothesis ($\mathfrak{c} = \aleph_1$),
$2^{\aleph_0} \not\to [\aleph_1]^2_3$.

This is Erdős's original positive contribution; the $100 prize was for deciding the
question without assuming CH.
-/
@[category research solved, AMS 3]
theorem erdos_under_ch (hCH : 𝔠 = ℵ_ 1) :
    ¬ cardinalBracketRamsey2 (𝔠) (ℵ_ 1) 3 := by
  sorry

/--
**Shelah [Sh88] consistency.** It is consistent with ZFC (with very large
$\mathfrak{c}$) that $2^{\aleph_0} \to [\aleph_1]^2_3$ holds.

Stated here as the existence of a witnessing setting: Shelah constructs a forcing
extension in which the positive bracket partition relation holds. We express this as
"`cardinalBracketRamsey2 (𝔠) (ℵ_ 1) 3` is consistent" by stating it as a *possible*
property (not provable nor refutable in ZFC). The Lean-side encoding is the
mathematical statement, with the consistency aspect documented above.
-/
@[category research solved, question, AMS 3]
theorem shelah_consistent : cardinalBracketRamsey2 (𝔠) (ℵ_ 1) 3 := by
  sorry

/--
**Specific Vaughan question [Va99, 7.81]** (still open).

Is it consistent with $\mathfrak{c} = \aleph_2$ that $2^{\aleph_0} \not\to [\aleph_1]^2_3$?

This narrows the open question to a specific cardinal arithmetic regime (intermediate
between Erdős's CH case and Shelah's very-large-$\mathfrak{c}$ case).
-/
@[category research open, question, AMS 3]
theorem vaughan_aleph_two :
    (𝔠 = ℵ_ 2 ∧ ¬ cardinalBracketRamsey2 (𝔠) (ℵ_ 1) 3) := by
  sorry

end erdos_474.variants

/- ### Sanity checks -/

/-- **Monotonicity in the color count.** If the bracket relation holds with $r$ colors,
it holds with any $r' \ge r$ colors: more colors only make missing one easier. -/
@[category test, AMS 3]
theorem cardinalBracketRamsey2_mono_colors {α β : Cardinal.{u}} {r r' : ℕ}
    (hr : 0 < r) (h : cardinalBracketRamsey2 α β r) (hrr' : r ≤ r') :
    cardinalBracketRamsey2 α β r' := by
  intro X hX f hsym
  sorry

/-- **Monotonicity in the subset size.** If the bracket relation holds for target $\beta$,
it holds for any $\beta' \le \beta$: smaller target is easier. -/
@[category test, AMS 3]
theorem cardinalBracketRamsey2_mono_target {α β β' : Cardinal.{u}} {r : ℕ}
    (h : cardinalBracketRamsey2 α β r) (hβ : β' ≤ β) :
    cardinalBracketRamsey2 α β' r := by
  intro X hX f hsym
  obtain ⟨Y, hY, c, hc⟩ := h X hX f hsym
  obtain ⟨Z, hZsub, hZcard⟩ := (Cardinal.le_mk_iff_exists_subset).mp (hY ▸ hβ)
  exact ⟨Z, hZcard, c, fun x hx y hy hne => hc x (hZsub hx) y (hZsub hy) hne⟩

end Erdos474
