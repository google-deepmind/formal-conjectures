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
# Erdős Problem 1046

*References:*
- [erdosproblems.com/1046](https://www.erdosproblems.com/1046)
- [EHP58] Erdős, P. and Herzog, F. and Piranian, G., *Metric properties of polynomials*. J.
  Analyse Math. (1958), 125-148.
- [Po59] Pommerenke, Ch., *On some problems by Erdős, Herzog and Piranian*. Michigan Math. J.
  (1959), 221-225.
-/

@[expose] public section

open Polynomial Metric

namespace Erdos1046

/-- The open unit lemniscate $E = \{z : \lvert f(z)\rvert < 1\}$ of a complex polynomial. -/
def lemniscate (f : ℂ[X]) : Set ℂ := {z | ‖f.eval z‖ < 1}

/-- The closed unit lemniscate $\{z : \lvert f(z)\rvert \leq 1\}$ of a complex polynomial. -/
def closedLemniscate (f : ℂ[X]) : Set ℂ := {z | ‖f.eval z‖ ≤ 1}

/--
Let $f\in \mathbb{C}[x]$ be a monic polynomial and
$$E=\{ z: \lvert f(z)\rvert <1\}.$$
If $E$ is connected then is $E$ contained in a disc of radius $2$?

A problem of Erdős, Herzog, and Piranian [EHP58], who also ask, if
$\{ z: \lvert f(z)\rvert\leq 1\}$ is connected, then what are the least possible diameter and
greatest possible width of this set, and conjecture the answer is $2$ in both cases. Their guess
that the width is always at most $2$ is false, as Pommerenke [Po59] gave an example with width
$>\sqrt{3}2^{1/3}\approx 2.18$.

The condition that $E$ is connected is equivalent to $E$ containing all zeros of $f'$.

The answer is yes, and in fact the centre of this disc can be taken to be
$\frac{z_1+\cdots+z_n}{n}$, where the $z_i$ are the roots of $f$, as shown by Pommerenke [Po59].
-/
@[category research solved, AMS 30, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1046.lean#L329"]
theorem erdos_1046 : answer(True) ↔ ∀ f : ℂ[X], f.Monic → IsConnected (lemniscate f) →
    ∃ c : ℂ, lemniscate f ⊆ ball c 2 := by
  sorry

/--
Pommerenke [Po59] showed that the centre of the disc can be taken to be the centroid
$\frac{z_1+\cdots+z_n}{n}$ of the roots $z_i$ of $f$.
-/
@[category research solved, AMS 30, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1046.lean#L321"]
theorem erdos_1046.variants.centroid : ∀ f : ℂ[X], f.Monic → IsConnected (lemniscate f) →
    lemniscate f ⊆ ball (f.roots.sum / f.natDegree) 2 := by
  sorry

/--
Erdős, Herzog, and Piranian [EHP58] conjecture that if $\{ z: \lvert f(z)\rvert\leq 1\}$ is
connected then its diameter is at least $2$.
-/
@[category research open, AMS 30]
theorem erdos_1046.variants.diameter : answer(sorry) ↔ ∀ f : ℂ[X], f.Monic →
    IsConnected (closedLemniscate f) → 2 ≤ Metric.ediam (closedLemniscate f) := by
  sorry

end Erdos1046
