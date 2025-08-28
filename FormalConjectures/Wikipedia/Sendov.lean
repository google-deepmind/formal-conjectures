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
# Sendov's conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Sendov%27s_conjecture)

Tags: Sendov Conjecture, Ilieff's Conjecture.

-/

open Polynomial

namespace Sendov

open Sendov

/-- The predicate that a polynomial satisfies the hypotheses of Sendov's conjecture.

`f.IsSendov` holds if `f` has degree at least 2 and all roots of `f` lie in the unit disc
of the complex plane. -/
private def Polynomial.IsSendov (f : ℂ[X]) : Prop :=
  2 ≤ f.natDegree ∧ (f.rootSet ℂ ⊆ Metric.closedBall 0 1)

/-- `SatisfiesSendovConjecture n` states that Sendov's conjecture is true for every polynomial of
degree `n`. -/
private def Nat.SatisfiesSendovConjecture (n : ℕ) : Prop :=
  ∀ (f : ℂ[X]), f.IsSendov → f.natDegree = n →
    ∀ z, z ∈ f.rootSet ℂ → Metric.infDist z (f.derivative.rootSet ℂ) ≤ 1

/-- **Sendov's conjecture** states that for a polynomial
$$f(z)=(z-r_{1})\cdots (z-r_{n}),\qquad (n\geq 2)$$
with all roots $r_1, ..., r_n$ inside the closed unit disk $|z| ≤ 1$, each of the $n$ roots is at a
distance no more than $1$ from at least one critical point.-/
@[category research open, AMS 12 30 52]
theorem sendov_conjecture (n : ℕ) (hn : 2 ≤ n) : n.SatisfiesSendovConjecture := by
  sorry

/-- **Sendov's conjecture** states that for a polynomial
$$f(z)=(z-r_{1})\cdots (z-r_{n}),\qquad (n\geq 2)$$
with all roots $r_1, ..., r_n$ inside the closed unit disk $|z| ≤ 1$, each of the $n$ roots is at a
distance no more than $1$ from at least one critical point.

It has been shown that Sendov's conjecture holds when the degree of $n$ is at most $9$.
-/
@[category research solved, AMS 12 30 52]
theorem sendov_conjecture.variants.le_nine (n : ℕ) (hn : n ∈ Set.Icc 2 9) :
    n.SatisfiesSendovConjecture := by
  sorry

/-- **Sendov's conjecture** states that for a polynomial
$$f(z)=(z-r_{1})\cdots (z-r_{n}),\qquad (n\geq 2)$$
with all roots $r_1, ..., r_n$ inside the closed unit disk $|z| ≤ 1$, each of the $n$ roots is at a
distance no more than $1$ from at least one critical point.

It has been shown that Sendov's conjecture holds for polynomials of sufficiently large degree.
-/
@[category research solved, AMS 12 30 52]
theorem sendov_conjecture.variants.eventually_true :
    ∀ᶠ (n : ℕ) in Filter.atTop, n.SatisfiesSendovConjecture := by
  sorry

end Sendov
