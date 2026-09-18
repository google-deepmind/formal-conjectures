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
# Erdős Problem 1147

*References:*
- [erdosproblems.com/1147](https://www.erdosproblems.com/1147)
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference "Paul
  Erdős and his mathematics", Budapest, July 1999 (1999).
- [Ko16b] Konieczny, Jakub, *Sets of recurrence as bases for the positive integers*. Acta Arith.
  (2016), 309-338.
-/

@[expose] public section

open Filter MeasureTheory

namespace Erdos1147

/-- The set $\{ n\geq 1: \| \alpha n^2\| < \epsilon(n)\}$. -/
def recurrenceSet (α : ℝ) (ε : ℕ → ℝ) : Set ℕ :=
  {n | 1 ≤ n ∧ distToNearestInt (α * n ^ 2) < ε n}

/--
Let $\alpha>0$ be an irrational number. Is the set
$$A=\left\{ n\geq 1: \| \alpha n^2\| < \frac{1}{\log n}\right\},$$
where $\|\cdot\|$ denotes the distance to the nearest integer, an additive basis of order $2$?

This was disproved by Konieczny [Ko16b], and is false both for almost every $\alpha>0$, and also
is false specifically for $\alpha=\sqrt{2}$.

More generally, given any $\epsilon(n)\to 0$, the set
$A=\{ n\geq 1: \| \alpha n^2\| < \epsilon(n)\}$ is not an additive basis of order $2$ for almost
every $\alpha>0$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1147.lean#L538"]
theorem erdos_1147 : answer(False) ↔ ∀ α : ℝ, 0 < α → Irrational α →
    (recurrenceSet α fun n ↦ 1 / Real.log n).IsAsymptoticAddBasisOfOrder 2 := by
  sorry

/-- Konieczny [Ko16b] showed that the set is not an additive basis of order $2$ for
$\alpha=\sqrt{2}$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1147.lean#L531"]
theorem erdos_1147.variants.sqrt_two :
    ¬ (recurrenceSet (√2) fun n ↦ 1 / Real.log n).IsAsymptoticAddBasisOfOrder 2 := by
  sorry

/--
Konieczny [Ko16b] showed that, given any $\epsilon(n)\to 0$, the set
$\{ n\geq 1: \| \alpha n^2\| < \epsilon(n)\}$ is not an additive basis of order $2$ for almost
every $\alpha>0$.
-/
@[category research solved, AMS 11]
theorem erdos_1147.variants.almost_every : ∀ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) →
    ∀ᵐ α : ℝ, 0 < α → ¬ (recurrenceSet α ε).IsAsymptoticAddBasisOfOrder 2 := by
  sorry

end Erdos1147
