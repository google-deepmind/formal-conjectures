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

See also Problems 897 and 1122.

[Er46] Erdős, P., _On the distribution function of additive functions_. Ann. of Math. (2) 47
(1946), 1-20.

[Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. **6**
(1961), 221–254.

[Er72] Erdős, P., _Quelques problèmes de théorie des nombres_, p. 81, 1972.

[Er82e] Erdős, P., _Some new problems and results in number theory_ (1982).

[Wi70] Wirsing, E., _A characterization of $\log n$ as an additive arithmetic function_.
Symposia Math. (1970), 45–47.
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

/--
Erdős (1946) [Er46]: If $f$ is an additive function and $f(n+1) - f(n) = o(1)$
(i.e., the differences tend to zero), then $f(n) = c \log n$ for some constant $c$
(exact equality, not just up to $O(1)$). This is a stronger hypothesis giving a
stronger conclusion than the main problem.
-/
@[category research solved, AMS 11]
theorem erdos_491_small_o : ∀ f : ℕ → ℝ, IsAdditiveArithmeticFunction f →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |f (n + 1) - f n| < ε) →
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → f n = c * Real.log (n : ℝ) := by
  sorry

/--
Erdős (1946) [Er46]: If $f$ is an additive function and $f$ is monotone non-decreasing
(i.e., $f(n+1) \geq f(n)$ for all $n$), then $f(n) = c \log n$ for some constant $c$.
-/
@[category research solved, AMS 11]
theorem erdos_491_monotone : ∀ f : ℕ → ℝ, IsAdditiveArithmeticFunction f →
    (∀ n : ℕ, f n ≤ f (n + 1)) →
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → f n = c * Real.log (n : ℝ) := by
  sorry

end Erdos491
