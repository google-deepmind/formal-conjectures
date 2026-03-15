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
import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 1134

*Reference:* [erdosproblems.com/1134](https://www.erdosproblems.com/1134)

Let $A \subseteq \mathbb{N}$ be the smallest set which contains $1$ and is closed under the
operations $x \mapsto 2x+1$, $x \mapsto 3x+1$, and $x \mapsto 6x+1$. Does $A$ have positive
lower density?

This was disproved by Crampin and Hilton, who showed that
$|A \cap [1,X]| \ll X^{\tau+o(1)}$ where $\tau \approx 0.900626 < 1$ is the unique positive
root of $6^{-\tau} + \sum_{k \geq 0} (3 \cdot 2^k)^{-\tau} = 1$. In particular, $A$ has
density $0$.

OEIS: [A185661](https://oeis.org/A185661)

[Gu83b] Guy, R. K., _Unsolved Problems: Don't Try to Solve These Problems_. American Mathematical
Monthly (1983), 35-41.

[Gu04] Guy, R. K., _Unsolved problems in number theory_ (2004), xviii+437.

[Kl82] Klarner, D. A., _A sufficient condition for certain semigroups to be free_. Journal of
Algebra (1982), 140-148.

[KlRa74] Klarner, D. A. and Rado, R., _Arithmetic properties of certain recursively defined sets_.
Pacific Journal of Mathematics (1974), 445-463.

[La16] Lagarias, J. C., _Erdős, Klarner, and the $3x+1$ problem_. Amer. Math. Monthly (2016),
753-776.
-/

open Filter

open scoped Topology

namespace Erdos1134

/-- The set $A$ from Erdős Problem 1134: the smallest subset of $\mathbb{N}$ containing $1$
and closed under $x \mapsto 2x+1$, $x \mapsto 3x+1$, and $x \mapsto 6x+1$. -/
inductive InSet : ℕ → Prop where
  | base : InSet 1
  | step2 (n : ℕ) : InSet n → InSet (2 * n + 1)
  | step3 (n : ℕ) : InSet n → InSet (3 * n + 1)
  | step6 (n : ℕ) : InSet n → InSet (6 * n + 1)

/-- The set $A$ from Problem 1134 as a `Set ℕ`. -/
def A : Set ℕ := {n : ℕ | InSet n}

/--
Erdős Problem 1134 [La16][KlRa74][Kl82][Gu83b][Gu04]:

Let $A \subseteq \mathbb{N}$ be the smallest set containing $1$ and closed under $x \mapsto 2x+1$,
$x \mapsto 3x+1$, and $x \mapsto 6x+1$. Does $A$ have positive lower density?

Disproved (answered in the negative) by Crampin and Hilton, who showed
$|A \cap [1,X]| \ll X^{\tau+o(1)}$ where $\tau \approx 0.900626 < 1$.
-/
@[category research solved, AMS 11]
theorem erdos_1134 : A.lowerDensity = 0 := by sorry

/-- Klarner's variant from Erdős Problem 1134:

Consider the smallest set $B \subseteq \mathbb{N}$ containing $0$ and closed under $x \mapsto 2x$,
$x \mapsto 3x+2$, and $x \mapsto 6x+3$. Does $B$ have positive density?

This variant, attributed to Klarner, remains open. It appears as Problem E36 in Guy's collection
and is discussed in Section 8.9 of Lagarias [La16]. -/
inductive InSetKlarner : ℕ → Prop where
  | base : InSetKlarner 0
  | step2 (n : ℕ) : InSetKlarner n → InSetKlarner (2 * n)
  | step3 (n : ℕ) : InSetKlarner n → InSetKlarner (3 * n + 2)
  | step6 (n : ℕ) : InSetKlarner n → InSetKlarner (6 * n + 3)

/-- The set $B$ from Klarner's variant as a `Set ℕ`. -/
def B : Set ℕ := {n : ℕ | InSetKlarner n}

@[category research open, AMS 11]
theorem erdos_1134_variant_klarner : answer(sorry) ↔ B.HasPosDensity := by sorry

end Erdos1134
