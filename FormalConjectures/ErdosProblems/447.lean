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
# Erdős Problem 447

*Reference:* [erdosproblems.com/447](https://www.erdosproblems.com/447)

How large can a union-free collection $\mathcal{F}$ of subsets of $[n]$ be? Erdős conjectured
that $|\mathcal{F}| < (1 + o(1)) \binom{n}{\lfloor n/2 \rfloor}$.

Solved by Kleitman [Kl71], who proved the conjectured bound.

[Kl71] Kleitman, D., *No four subsets forming an N*, J. Combinatorial Theory Ser. A 5 (1968),
313-318.
-/

namespace Erdos447

/-- A family of finsets is union-free if there are no three distinct members
$A$, $B$, $C$ with $A \cup B = C$. -/
def UnionFreeFamily {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F, A ≠ B → A ≠ C → B ≠ C → A ∪ B ≠ C

/-- Erdős Problem 447 (Kleitman's Theorem [Kl71]):
For every $\varepsilon > 0$, there exists $N_0$ such that for all $n \geq N_0$, if $\mathcal{F}$
is a union-free family of subsets of $\{1, \ldots, n\}$, then
$$|\mathcal{F}| \leq (1 + \varepsilon) \binom{n}{\lfloor n/2 \rfloor}.$$ -/
@[category research solved, AMS 5]
theorem erdos_447 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∀ F : Finset (Finset (Fin n)),
    UnionFreeFamily F →
    (F.card : ℝ) ≤ (1 + ε) * (Nat.choose n (n / 2) : ℝ) := by
  sorry

end Erdos447
