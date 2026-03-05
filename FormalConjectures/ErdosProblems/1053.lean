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
# Erdős Problem 1053

*Reference:* [erdosproblems.com/1053](https://www.erdosproblems.com/1053)

Call a number $k$-perfect if $\sigma(n) = kn$, where $\sigma(n)$ is the sum of the divisors
of $n$. Must $k = o(\log \log n)$?

A question of Erdős, as reported in problem B2 of Guy's collection.

[Gu04] Guy, R., *Unsolved Problems in Number Theory*, 3rd edition, Springer, 2004.
-/

open Finset Real

namespace Erdos1053

/-- The sum-of-divisors function $\sigma(n) = \sum_{d \mid n} d$. -/
def sumOfDivisors (n : ℕ) : ℕ :=
  (Nat.divisors n).sum id

/-- A natural number $n$ is $k$-perfect if $n \geq 1$ and $\sigma(n) = k \cdot n$. -/
def IsMultiplyPerfect (n k : ℕ) : Prop :=
  n ≥ 1 ∧ sumOfDivisors n = k * n

/--
Erdős Problem 1053 [Gu04]:

If $n$ is a $k$-perfect number ($\sigma(n) = kn$), must $k = o(\log \log n)$ as $n \to \infty$
among multiply perfect numbers?

Equivalently: for every $\varepsilon > 0$, the set of multiply perfect numbers $n$
with $\sigma(n)/n \geq \varepsilon \cdot \log(\log(n))$ is finite.
-/
@[category research open, AMS 11]
theorem erdos_1053 : answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 →
    Set.Finite {n : ℕ | ∃ k : ℕ, IsMultiplyPerfect n k ∧
      (k : ℝ) ≥ ε * Real.log (Real.log (n : ℝ))} := by
  sorry

end Erdos1053
