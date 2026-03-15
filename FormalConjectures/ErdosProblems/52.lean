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
# Erdős Problem 52

*Reference:* [erdosproblems.com/52](https://www.erdosproblems.com/52)

The Erdős–Szemerédi sum-product conjecture [ErSz83]: for every $\varepsilon > 0$ there exists
$c > 0$ such that $\max(|A+A|, |A \cdot A|) \geq c \cdot |A|^{2-\varepsilon}$ for every finite
set $A$ of integers. The best known bound is due to Bloom [Bl25].

[ErSz83] Erdős, P. and Szemerédi, E., _On sums and products of integers_.
Studies in pure mathematics, Birkhäuser, Basel (1983), 213–218.

[Bl25] Bloom, T. F., _Control and its applications in additive combinatorics_.
arXiv:2501.09470 (2025).
-/

open Finset Real

open scoped Pointwise

namespace Erdos52

/--
**Erdős Problem #52** (The Sum-Product Conjecture):

For every $\epsilon > 0$, there exists $c > 0$ such that for every finite set
$A$ of integers with $|A| \geq 2$,
$$\max(|A + A|, |A \cdot A|) \geq c \cdot |A|^{2 - \epsilon}.$$

A problem of Erdős and Szemerédi [ErSz83]. The current best lower bound is
$\max(|A+A|, |AA|) \gg |A|^{1270/951 - o(1)}$ due to Bloom [Bl25].
-/
@[category research open, AMS 5 11]
theorem erdos_52 :
    ∀ ε : ℝ, ε > 0 →
    ∃ c : ℝ, c > 0 ∧
    ∀ A : Finset ℤ, (A.card : ℝ) ≥ 2 →
    max ((A + A).card : ℝ) ((A * A).card : ℝ) ≥ c * (A.card : ℝ) ^ (2 - ε) := by
  sorry

end Erdos52
