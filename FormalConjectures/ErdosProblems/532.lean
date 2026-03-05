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
# Erdős Problem 532

*Reference:* [erdosproblems.com/532](https://www.erdosproblems.com/532)

If $\mathbb{N}$ is 2-coloured then is there some infinite set $A\subseteq \mathbb{N}$
such that all finite subset sums $\sum_{n\in S}n$ (as $S$ ranges over all non-empty
finite subsets of $A$) are monochromatic?

In other words, must some colour class be an IP set. Asked by Graham and Rothschild.

Proved by Hindman [Hi74] for any number of colours. This is now known as
**Hindman's theorem** (or the Finite Sums theorem).

See also [531] for the finite version (Folkman numbers).

[Hi74] Hindman, N., _Finite sums from sequences within cells of a partition of N_,
Journal of Combinatorial Theory, Series A **17** (1974), 1-11.
-/

open Finset BigOperators

namespace Erdos532

/-- **Hindman's theorem** (Erdős Problem 532, [Hi74]):
For any 2-colouring $\chi$ of the natural numbers, there exists an infinite set
$A$ of positive naturals such that all non-empty finite subset sums of elements
of $A$ are monochromatic. -/
@[category research solved, AMS 5]
theorem erdos_532 : answer(True) ↔
    ∀ χ : ℕ → Bool, ∃ (A : Set ℕ), A.Infinite ∧ (∀ a ∈ A, 0 < a) ∧
    ∃ c : Bool, ∀ S : Finset ℕ, S.Nonempty → (↑S : Set ℕ) ⊆ A →
      χ (∑ i ∈ S, i) = c := by
  sorry

end Erdos532
