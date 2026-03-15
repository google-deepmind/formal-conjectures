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

See also [531] for the finite version (Folkman numbers) and [948].

[Er73] Erdős, P., _Problems and results on combinatorial number theory_. In: A Survey of
Combinatorial Theory (1973), 117–138.

[Er75b] Erdős, P., _Problems and results in combinatorial number theory_. Journées
Arithmétiques de Bordeaux (Conf., Univ. Bordeaux, Bordeaux, 1974) (1975), 295–310.

[Er77c] Erdős, P., _Problems and results on combinatorial number theory. III._. Number Theory Day
(Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43–72.

[Hi74] Hindman, N., _Finite sums from sequences within cells of a partition of N_,
Journal of Combinatorial Theory, Series A **17** (1974), 1–11.
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

/-- **Hindman's theorem (general version)** (Erdős Problem 532, [Hi74]):
For any finite colouring $\chi : \mathbb{N} \to \mathrm{Fin}\, r$ with $r \geq 1$,
there exists an infinite set $A$ of positive naturals such that all non-empty finite
subset sums of elements of $A$ are monochromatic.
This is the full strength of Hindman's theorem, generalising `erdos_532` from 2 colours
to any finite number of colours. -/
@[category research solved, AMS 5]
theorem erdos_532_general (r : ℕ) (hr : 0 < r) (χ : ℕ → Fin r) :
    ∃ (A : Set ℕ), A.Infinite ∧ (∀ a ∈ A, 0 < a) ∧
    ∃ c : Fin r, ∀ S : Finset ℕ, S.Nonempty → (↑S : Set ℕ) ⊆ A →
      χ (∑ i ∈ S, i) = c := by
  sorry

end Erdos532
