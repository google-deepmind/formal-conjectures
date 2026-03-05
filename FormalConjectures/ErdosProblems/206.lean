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
# Erdős Problem 206

*Reference:* [erdosproblems.com/206](https://www.erdosproblems.com/206)

[Ko24b] Kovač, V., _Disproof of a conjecture of Erdős and Graham on the greedy algorithm for
Egyptian fractions_ (2024).
-/

open scoped BigOperators

open MeasureTheory

namespace Erdos206

/--
The sum of unit fractions with denominators from a finset of naturals:
$\sum_{m \in S} 1/m$.
-/
noncomputable def unitFracSum (S : Finset ℕ) : ℝ :=
  ∑ m ∈ S, (1 : ℝ) / (m : ℝ)

/--
$R_n(x)$: the maximal sum of $n$ distinct unit fractions (with positive integer
denominators) that is strictly less than $x$.
-/
noncomputable def bestUnderapprox (n : ℕ) (x : ℝ) : ℝ :=
  sSup {s : ℝ | ∃ S : Finset ℕ, S.card = n ∧ (∀ m ∈ S, 0 < m) ∧
    s = unitFracSum S ∧ s < x}

/--
A real number $x > 0$ is "eventually greedy" if there exists $N_0$ such that for
all $n \geq N_0$, every set $S$ of $n$ distinct positive integers achieving $R_n(x)$ can
be extended to achieve $R_{n+1}(x)$ by adding the smallest eligible new
denominator.
-/
def IsEventuallyGreedy (x : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ S : Finset ℕ,
      S.card = n →
      (∀ m ∈ S, 0 < m) →
      unitFracSum S < x →
      unitFracSum S = bestUnderapprox n x →
        ∃ k : ℕ, 0 < k ∧ k ∉ S ∧
          unitFracSum S + (1 : ℝ) / (k : ℝ) < x ∧
          unitFracSum S + (1 : ℝ) / (k : ℝ) = bestUnderapprox (n + 1) x ∧
          (∀ j : ℕ, 0 < j → j ∉ S →
            unitFracSum S + (1 : ℝ) / (j : ℝ) < x → k ≤ j)

/--
Erdős Problem 206 (Disproved by Kovač [Ko24b]):

Let $x > 0$ be a real number. For any $n \geq 1$ let $R_n(x)$ be the maximal sum of $n$
distinct unit fractions which is $< x$. Erdős and Graham asked whether, for
almost all $x$, the best underapproximations are eventually constructed in a
greedy fashion: $R_{n+1}(x) = R_n(x) + 1/m$ where $m$ is the smallest new
denominator keeping the sum below $x$.

Kovač proved this is false — the set of $x \in (0,\infty)$ for which the best
underapproximations are eventually greedy has Lebesgue measure zero.

We formalize Kovač's result (the negation of the original conjecture).
-/
@[category research solved, AMS 11 28]
theorem erdos_206 :
    volume {x : ℝ | 0 < x ∧ IsEventuallyGreedy x} = 0 := by
  sorry

end Erdos206
