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

Does the negative square-bracket partition relation 2^ℵ₀ ↛ [ℵ₁]³₃ hold assuming the continuum
equals ℵ₂?

[Er95d] Erdős, P., *Problems and results on graphs and hypergraphs: similarities and
differences* (1995), p.64.

[Va99] Väänänen, J., *Problems from the Erdős notebook* (1999), 7.81.

[Sh88] Shelah, S., *Was Sierpiński right? I*. Israel Journal of Mathematics (1988), 355–380.

Erdős offered $100 for deciding the answer without CH.
-/

open Cardinal

namespace Erdos474

/-- The negative square-bracket partition relation $\kappa \nrightarrow [\mu]_k^2$ for cardinals.

There exists a $k$-coloring of pairs from a set of cardinality $\kappa$ such that
every subset of cardinality $\geq \mu$ contains pairs of all $k$ colors.

In standard Erdős-Rado partition calculus notation, this is
$\kappa \nrightarrow [\mu]_k^2$. -/
def NegSqBracketPartition (κ μ : Cardinal) (k : ℕ) : Prop :=
  ∃ (α : Type*) (_ : #α = κ) (f : α → α → Fin k),
    (∀ x y, f x y = f y x) ∧
    ∀ (S : Set α), #S ≥ μ →
      ∀ c : Fin k, ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ f a b = c

/--
Erdős Problem 474 (1954) [Er95d, p.64] [Va99, 7.81]:

Does the negative square-bracket partition relation $2^{\aleph_0} \nrightarrow [\aleph_1]_3^2$
hold assuming $\mathfrak{c} = \aleph_2$?

In words: can the pairs from $\mathbb{R}$ be $3$-colored so that every uncountable
subset contains pairs of each color?

Sierpinski and Kurepa independently proved the $2$-color version
($2^{\aleph_0} \nrightarrow [\aleph_1]_2^2$) holds in ZFC. Erdős proved that under the
continuum hypothesis ($\mathfrak{c} = \aleph_1$), the $3$-color version holds, and offered
100 dollars for deciding what happens without CH.

Shelah [Sh88] showed it is consistent without CH that the positive relation
$2^{\aleph_0} \to [\aleph_1]_3^2$ holds, but with $\mathfrak{c}$ very large.

The specific remaining open question (asked in [Va99]):
Assuming $\mathfrak{c} = \aleph_2$, does $2^{\aleph_0} \nrightarrow [\aleph_1]_3^2$ hold?
-/
@[category research open, AMS 3 5]
theorem erdos_474 : answer(sorry) ↔
    (continuum = aleph 2 → NegSqBracketPartition continuum (aleph 1) 3) := by
  sorry

end Erdos474
