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

import FormalConjecturesUtil

/-!
# Erdős Problem 655

*Reference:* [erdosproblems.com/655](https://www.erdosproblems.com/655)
-/

open Filter Finset EuclideanGeometry

namespace Erdos655

/-- A collection $x_1, \dots, x_n\in\mathbb{R}^2$ is _valid_ if
no circle whose centre is one of the $x_i$ contains three other points. -/
def IsValid (X : Finset ℝ²) : Prop :=
  ∀ᵉ (x ∈ X) (r > 0), ¬3 ≤ (Metric.sphere x r ∩ X).ncard

/--
Let $x_1,\ldots,x_n\in \mathbb{R}^2$ be such that no circle whose centre is one
of the $x_i$ contains three other points. Are there at least
$$(1+c)\frac{n}{2}$$
distinct distances determined between the $x_i$, for some constant $c>0$ and
all $n$ sufficiently large?

The answer is **no**: as Zach Hunter observed, the regular `n`-gon (`n` points equally spaced on a
circle) is valid and determines only `⌊n/2⌋ < (1+c)n/2` distinct distances, for every `c > 0`.
(In the spirit of related conjectures of Erdős and others, presumably some kind of assumption that
the points are in general position was intended; see `erdos_655.variants.general_position`.)

The disproof — the regular `n`-gon construction together with its supporting lemmas — is formalised
at the linked commit. -/
@[category research solved, AMS 5 52, formal_proof using formal_conjectures at "https://github.com/AlperTheKing/formal-conjectures/blob/4aaaf544b6ed0ef22580787a8d8a19e85dc49556/FormalConjectures/ErdosProblems/655.lean"]
theorem erdos_655 :
    answer(False) ↔ ∃ c > (0 : ℝ), ∀ᶠ n in atTop, ∀ (X : Finset ℝ²), #X = n → IsValid X →
      (1 + c) * n / 2 ≤ distinctDistances X := by
  sorry

/-- Let $x_1,\ldots,x_n\in \mathbb{R}^2$ be such that no circle whose centre is one
of the $x_i$ contains three other points. Are there at least$$(1+c)\frac{n}{2}$$
distinct distances determined between the $x_i$, for some constant $c>0$ and
all $n$ sufficiently large?

In the spirit of related conjectures of Erdős and others, presumably
some kind of assumption that the points are in general position
(e.g. no three on a line and no four on a circle) was intended.-/
@[category research open, AMS 5 52]
theorem erdos_655.variants.general_position :
    answer(sorry) ↔ ∃ c > (0 : ℝ), ∀ᶠ n in atTop, ∀ (X : Finset ℝ²), #X = n → IsValid X →
      InGeneralPosition X → (1 + c) * n / 2 ≤ distinctDistances X := by
  sorry

end Erdos655
