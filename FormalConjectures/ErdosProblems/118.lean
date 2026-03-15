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
# Erdős Problem 118

*Reference:* [erdosproblems.com/118](https://www.erdosproblems.com/118)

Erdős–Hajnal conjecture on partition ordinals (disproved): if $\alpha \to (\alpha, 3)^2$, does
$\alpha \to (\alpha, n)^2$ hold for all $n \geq 3$? Independently disproved by Schipperus and
Darby.

[Er87] Erdős, P., *Some of my favourite problems in various branches of combinatorics*.

[Er90] Erdős, P., *Some of my favourite problems in number theory, combinatorics, and geometry*.

[Er95d] Erdős, P., *Problems and results on finite and infinite combinatorial analysis*.

[Er97f] Erdős, P., *Some problems on finite and infinite graphs*.

[Sc99] Schipperus, R., *Countable partition ordinals*, PhD thesis, University of Colorado
at Boulder, 1999.

[Sc10] Schipperus, R., *Countable partition ordinals*, Ann. Pure Appl. Logic 161 (2010),
no. 10, 1195–1215.

[Da99] Darby, C., *Negative partition relations for ordinals $\omega^{\omega^\alpha}$*,
J. Combin. Theory Ser. B (1999), 205–222.

[La00] Larson, J.A., *An ordinal partition avoiding pentagrams*, J. Symbolic Logic (2000),
969–978.

[HST10] Hajnal, A. and Larson, J.A., *Partition relations*, in: Handbook of Set Theory,
Springer, 2010.

See also Erdős problems 590, 591, 592.
-/

open Ordinal

namespace Erdos118

/-- The "underlying type" of ordinal $\alpha$: the set of all ordinals strictly less
than $\alpha$, linearly ordered by the natural ordering on ordinals. -/
abbrev OrdinalSet (α : Ordinal) := {a : Ordinal // a < α}

/-- The ordinal partition relation $\alpha \to (\beta, \gamma)^2$:
every $2$-coloring of the pairs of elements of $\alpha$ (viewed as the set of
ordinals less than $\alpha$) contains either:
- an order-embedded copy of $\beta$ whose pairs are all colored $0$ (red), or
- an order-embedded copy of $\gamma$ whose pairs are all colored $1$ (blue).

Here a "copy of $\beta$" is given by an order embedding
$e : \operatorname{OrdinalSet}(\beta) \hookrightarrow \operatorname{OrdinalSet}(\alpha)$,
and monochromaticity means $f(e(i), e(j)) = c$ for all $i < j$. -/
def OrdPartition (α β γ : Ordinal) : Prop :=
  ∀ (f : OrdinalSet α → OrdinalSet α → Fin 2),
    (∃ e : OrdinalSet β ↪o OrdinalSet α,
      ∀ i j : OrdinalSet β, i < j → f (e i) (e j) = 0) ∨
    (∃ e : OrdinalSet γ ↪o OrdinalSet α,
      ∀ i j : OrdinalSet γ, i < j → f (e i) (e j) = 1)

/--
Erdős–Hajnal Conjecture on Partition Ordinals (Problem 118)
[Er87, Er90, Er95d, Er97f] — **DISPROVED**

An ordinal $\alpha$ is called a *partition ordinal* if $\alpha \to (\alpha, 3)^2$, i.e., every
$2$-coloring of pairs from a linearly ordered set of order type $\alpha$ contains either
a monochromatic copy of $\alpha$ in color $0$ (red) or a monochromatic triangle $K_3$ in
color $1$ (blue).

Erdős and Hajnal conjectured that for every partition ordinal $\alpha$ and every $n \geq 3$,
we also have $\alpha \to (\alpha, n)^2$.

This conjecture is FALSE, as independently shown by Schipperus [Sc99] (published in
[Sc10]) and Darby [Da99]. For example, Larson [La00] showed that $\omega^{\omega^2}$ is a
partition ordinal — i.e., $\omega^{\omega^2} \to (\omega^{\omega^2}, 3)^2$ holds — but
$\omega^{\omega^2} \to (\omega^{\omega^2}, 5)^2$ fails.

See also Hajnal–Larson, Chapter 2.9 of [HST10] for background and proof sketches.
-/
@[category research solved, AMS 3 5]
theorem erdos_118 : answer(False) ↔ ∀ (α : Ordinal), OrdPartition α α 3 →
      ∀ n : ℕ, 3 ≤ n → OrdPartition α α (↑n) := by
  sorry

/--
Explicit counterexample to the Erdős–Hajnal conjecture (Problem 118):
$\omega^{\omega^2} \to (\omega^{\omega^2}, 3)^2$ holds (i.e., $\omega^{\omega^2}$ is a
partition ordinal), but $\omega^{\omega^2} \to (\omega^{\omega^2}, 5)^2$ fails.

This was shown by Larson [La00] (the partition ordinal property) and the failure for $n = 5$
follows from the counterexamples of Schipperus [Sc99, Sc10] and Darby [Da99].
-/
@[category research solved, AMS 3 5]
theorem erdos_118_counterexample :
    OrdPartition (ω ^ (ω ^ 2)) (ω ^ (ω ^ 2)) 3 ∧
    ¬ OrdPartition (ω ^ (ω ^ 2)) (ω ^ (ω ^ 2)) 5 := by
  sorry

end Erdos118
