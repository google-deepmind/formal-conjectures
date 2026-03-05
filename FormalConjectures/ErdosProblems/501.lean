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
# Erdős Problem 501

*Reference:* [erdosproblems.com/501](https://www.erdosproblems.com/501)

For every $x \in \mathbb{R}$, let $A_x \subset \mathbb{R}$ be a bounded set with outer measure
$< 1$. Must there exist an infinite independent set, that is, some infinite $X \subseteq \mathbb{R}$
such that $x \notin A_y$ for all $x \neq y \in X$?

If the sets $A_x$ are closed and have measure $< 1$, then must there exist an
independent set of size $3$?

Erdős and Hajnal proved the existence of arbitrarily large finite independent
sets (under the assumptions in the first problem). Hechler showed the answer
to the first question is no, assuming the continuum hypothesis. Newelski,
Pawlikowski, and Seredyński proved that if all the $A_x$ are closed with
measure $< 1$ then there is an infinite independent set.

[Er61] Erdős, P., _Problems in combinatorics_ (1961).

[ErHa71] Erdős, P. and Hajnal, A., _On a property of families of sets_ (1971).
-/

open MeasureTheory Set

namespace Erdos501

/-- A set $X$ is independent with respect to a family of sets $A$ if for all
distinct $x, y \in X$, we have $x \notin A(y)$. -/
def IndependentFamily (A : ℝ → Set ℝ) (X : Set ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → x ∉ A y

/--
Erdős Problem 501 [Er61][ErHa71]: If each $A_x$ is bounded with outer measure $< 1$, must
there exist an infinite independent set?

Hechler showed the answer is no assuming the continuum hypothesis. The full
ZFC status remains open.
-/
@[category research open, AMS 3 28]
theorem erdos_501 :
    answer(sorry) ↔
    ∀ A : ℝ → Set ℝ,
      (∀ x : ℝ, Bornology.IsBounded (A x) ∧ volume (A x) < 1) →
      ∃ X : Set ℝ, X.Infinite ∧ IndependentFamily A X := by
  sorry

/--
Erdős Problem 501, closed variant [Er61][ErHa71]: If each $A_x$ is closed with
measure $< 1$, must there exist an independent set of size $3$?

Newelski, Pawlikowski, and Seredyński proved that under these hypotheses there
is in fact an infinite independent set.
-/
@[category research solved, AMS 3 28]
theorem erdos_501.variants.closed_measure :
    answer(True) ↔
    ∀ A : ℝ → Set ℝ,
      (∀ x : ℝ, IsClosed (A x) ∧ volume (A x) < 1) →
      ∃ x y z : ℝ, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
        IndependentFamily A {x, y, z} := by
  sorry

end Erdos501
