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
# Erdős Problem 635

*Reference:* [erdosproblems.com/635](https://www.erdosproblems.com/635)

Let $t \geq 1$ and $A \subseteq \{1, \ldots, N\}$ be such that whenever $a, b \in A$ with
$b - a \geq t$ we have $(b - a) \nmid b$. How large can $|A|$ be? Is it true that
$|A| \leq (1/2 + o(1)) \cdot N$?

Asked by Erdős in a letter to Ruzsa around 1980.

[Gu83] Guy, R. K., _Unsolved Problems in Number Theory_ (1983).

[Ru99] Ruzsa, I., related correspondence and results (1999).

[El79] Elliott, P. D. T. A., _Probabilistic Number Theory. I_ (1979).

When $t = 1$, the maximum is $\lfloor (N+1)/2 \rfloor$, achieved by taking $A$ to be all odd
numbers in $\{1, \ldots, N\}$. When $t = 2$, Erdős observed $|A| \geq N/2 + c \log N$ for
some $c > 0$, by taking $A$ to be the odd numbers together with $2^k$ for odd $k$.

The upper bound $|A| \leq (1/2 + o(1)) \cdot N$ has been resolved affirmatively
by ChatGPT-5.2 (prompted by Leeham). Tao observed that a positive answer also follows
from an inequality due to Elliott [El79].
-/

namespace Erdos635

/-- The divisibility-avoidance property with threshold $t$:
for all $a, b \in A$ with $b - a \geq t$, we require $(b - a) \nmid b$. -/
def DivAvoidance (A : Finset ℕ) (t : ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, b - a ≥ t → ¬(b - a ∣ b)

/-- The maximum cardinality of a subset of $\{1, \ldots, N\}$ satisfying the
divisibility-avoidance property with threshold $t$. -/
noncomputable def maxDivAvoidance (N t : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ DivAvoidance A t ∧ A.card = k}

/--
When $t = 1$, the maximum size of a divisibility-avoidance set in $\{1, \ldots, N\}$
is exactly $\lfloor (N+1)/2 \rfloor$, achieved by taking all odd numbers. [Gu83][Ru99]
-/
@[category research solved, AMS 5 11]
theorem erdos_635.variants.t_eq_one (N : ℕ) (hN : N ≥ 1) :
    maxDivAvoidance N 1 = (N + 1) / 2 := by
  sorry

/--
When $t = 2$, there exists $c > 0$ such that there is a set $A \subseteq \{1, \ldots, N\}$
satisfying the divisibility-avoidance condition with $|A| \geq N/2 + c \cdot \log N$.
(Take $A$ to be the odd numbers together with $2^k$ for odd $k$.) [Gu83][Ru99]
-/
@[category research solved, AMS 5 11]
theorem erdos_635.variants.t_eq_two_lower :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (maxDivAvoidance N 2 : ℝ) ≥ (N : ℝ) / 2 + c * Real.log (N : ℝ) := by
  sorry

/--
For every $t \geq 1$ and $\varepsilon > 0$, there exists $N_0$ such that for all $N \geq N_0$,
every $A \subseteq \{1, \ldots, N\}$ satisfying the divisibility-avoidance property with
threshold $t$ has $|A| \leq (1/2 + \varepsilon) \cdot N$. [Gu83][Ru99][El79]

Resolved affirmatively by ChatGPT-5.2 (prompted by Leeham); Tao observed that a positive
answer also follows from an inequality due to Elliott [El79].

Equivalently, $\mathrm{maxDivAvoidance}(N, t) / N \to 1/2$ as $N \to \infty$ for any fixed $t$.
-/
@[category research solved, AMS 5 11]
theorem erdos_635 : answer(True) ↔
    ∀ t : ℕ, t ≥ 1 → ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
        ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
          DivAvoidance A t →
            (A.card : ℝ) ≤ (1 / 2 + ε) * (N : ℝ) := by
  sorry

end Erdos635
