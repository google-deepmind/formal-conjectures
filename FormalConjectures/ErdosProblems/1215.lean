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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 1215

*References:*
- [erdosproblems.com/1215](https://www.erdosproblems.com/1215)
- [EHP55] Erdős, P. and Herzog, F. and Piranian, G., *Polynomials whose zeros lie on the unit
  circle*. Duke Math. J. (1955), 347-351.
- [Co52] P. Cohen, *Modulus of an analytic function*. American Mathematical Monthly (1952),
  704-705.
- [Ma53] Mac Lane, Gerald R., *On a conjecture of Erdős, Herzog, and Piranian*. Michigan Math. J.
  (1953/54), 147-148.
-/

@[expose] public section

open Polynomial Set

namespace Erdos1215

/--
A polynomial `P` is *admissible* if `P(0) = 1`, `P` is nonconstant, and all its roots lie on the
unit circle.
-/
def IsAdmissible (P : ℂ[X]) : Prop :=
  P.eval 0 = 1 ∧ 0 < P.natDegree ∧ ∀ z : ℂ, P.IsRoot z → ‖z‖ = 1

/--
`γ : [0, 1] → ℂ` is a path in `{z : |P(z)| < 1}` connecting `0` to the unit circle. Since
`|P(0)| = 1`, the strict inequality is only required away from the starting point.
-/
def IsEscapePath (P : ℂ[X]) (γ : ℝ → ℂ) : Prop :=
  ContinuousOn γ (Icc 0 1) ∧ γ 0 = 0 ∧ ‖γ 1‖ = 1 ∧
    ∀ t ∈ Icc (0 : ℝ) 1, t ≠ 0 → ‖P.eval (γ t)‖ < 1

/--
Does there exist a constant $C$ such that for every polynomial $P$ with $P(0)=1$, all of whose
roots are on the unit circle, there exists a path in
$$\{ z: \lvert P(z)\rvert < 1\}$$
which connects $0$ to the unit circle of length at most $C$?

A problem of Erdős, Herzog, and Piranian. Cohen [Co52] proved that there always exists a path in
$\{ z: \lvert P(z)\rvert < 1\}$ which connects $0$ to the unit circle. Loewner proved (see
[EHP55]) the existence of such a polynomial $P$ such that every straight line connecting $0$ to
the unit circle contains $z$ with $\lvert P(z)\rvert>1$.

This was resolved in the negative by Mac Lane [Ma53], who proved that arbitrarily long parts of
any such path must be forced to lie an arbitrary neighbourhood of $0$. More precisely, for any
simply-connected compact $A\subset \{\lvert z\rvert <1\}$ with $0\not\in A$, for all sufficiently
large (depending on $n$) $d$ there exists such a polynomial $P$ of degree $d$ such that
$\lvert P(z)\rvert >2$ for all $z\in A$. One can then choose $A$ to be a suitable labyrinth
blocking $0$ from the unit circle, which any candidate path must traverse.

The length of a path is its total variation on $[0,1]$.
-/
@[category research solved, AMS 30, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1215.lean#L132"]
theorem erdos_1215 : answer(False) ↔ ∃ C : ℝ, ∀ P : ℂ[X], IsAdmissible P →
    ∃ γ : ℝ → ℂ, IsEscapePath P γ ∧ eVariationOn γ (Icc 0 1) ≤ ENNReal.ofReal C := by
  sorry

/-- Mac Lane [Ma53]: for every $L$ there is an admissible $P$ all of whose escape paths have
length $>L$. -/
@[category research solved, AMS 30, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1215.lean#L87"]
theorem erdos_1215.variants.mac_lane : ∀ L : ℝ, 0 ≤ L → ∃ P : ℂ[X], IsAdmissible P ∧
    ∀ γ : ℝ → ℂ, IsEscapePath P γ → ENNReal.ofReal L < eVariationOn γ (Icc 0 1) := by
  sorry

/-- Cohen [Co52] proved that there always exists a path in $\{ z: \lvert P(z)\rvert < 1\}$
which connects $0$ to the unit circle. -/
@[category research solved, AMS 30]
theorem erdos_1215.variants.cohen :
    ∀ P : ℂ[X], IsAdmissible P → ∃ γ : ℝ → ℂ, IsEscapePath P γ := by
  sorry

end Erdos1215
