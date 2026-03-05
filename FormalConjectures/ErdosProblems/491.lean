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
# Erdős Problem 491

*Reference:* [erdosproblems.com/491](https://www.erdosproblems.com/491)

If $f$ is an additive arithmetic function (i.e. $f(ab) = f(a) + f(b)$ whenever $\gcd(a,b) = 1$)
and there is a constant $c$ such that $|f(n+1) - f(n)| < c$ for all $n$, must there exist a
constant $c'$ such that $f(n) = c' \log n + O(1)$?

[Wi70] Wirsing, E., _A characterization of $\log n$ as an additive arithmetic function_, 1970.
-/

namespace Erdos491

/--
An additive arithmetic function: $f(ab) = f(a) + f(b)$ whenever $\gcd(a,b) = 1$.
-/
def IsAdditiveArithmeticFunction (f : ℕ → ℝ) : Prop :=
  ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a + f b

/--
Erdős Problem 491 (proved by Wirsing [Wi70]):

Let $f : \mathbb{N} \to \mathbb{R}$ be an additive function (i.e. $f(ab) = f(a) + f(b)$ whenever
$\gcd(a,b) = 1$). If there is a constant $c$ such that $|f(n+1) - f(n)| < c$ for
all $n$, then there exist constants $c'$ and $M$ such that $|f(n) - c' \log n| \leq M$
for all $n \geq 1$.
-/
@[category research solved, AMS 11]
theorem erdos_491 : answer(True) ↔
    ∀ f : ℕ → ℝ, IsAdditiveArithmeticFunction f →
    (∃ c : ℝ, ∀ n : ℕ, |f (n + 1) - f n| < c) →
    ∃ c' : ℝ, ∃ M : ℝ, ∀ n : ℕ, 1 ≤ n →
      |f n - c' * Real.log (n : ℝ)| ≤ M := by
  sorry

end Erdos491
