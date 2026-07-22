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

import FormalConjecturesUtil

/-!
# Erdős Problem 205

*References:*
- [erdosproblems.com/205](https://www.erdosproblems.com/205)
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [Ro34] Romanoff, N. P., *Über einige Sätze der additiven Zahlentheorie*. Math. Ann. (1934),
  668-678.
-/

open Asymptotics Filter

open scoped ArithmeticFunction.Omega

namespace Erdos205

/--
`IsRepresentable f n` states that `n` can be written as `2 ^ k + m` for some `k ≥ 0` where the
number of prime divisors of `m`, counted with multiplicity, is less than `f m`.
-/
def IsRepresentable (f : ℕ → ℝ) (n : ℕ) : Prop :=
  ∃ k m : ℕ, n = 2 ^ k + m ∧ (Ω m : ℝ) < f m

/--
Is it true that all sufficiently large $n$ can be written as $2^k+m$ for some $k\geq 0$, where
$\Omega(m)<\log\log m$? (Here $\Omega(m)$ is the number of prime divisors of $m$ counted with
multiplicity.)

Barreto and Leeham, using ChatGPT and Aristotle, have proved a negative answer, which was
quantified by Tao and Alexeev (see the comments): in fact there are infinitely many $n$ such that,
for all $k$ with $2^k<n$, $n-2^k$ has at least
\[\gg \left(\frac{\log n}{\log\log n}\right)^{1/2}\]
many prime factors.
-/
@[category research solved, AMS 11]
theorem erdos_205.parts.i : answer(False) ↔
    ∀ᶠ n : ℕ in atTop, IsRepresentable (fun m => Real.log (Real.log m)) n := by
  sorry

/--
Is it true that all sufficiently large $n$ can be written as $2^k+m$ for some $k\geq 0$, where
$\Omega(m)<\log\log m$? (Here $\Omega(m)$ is the number of prime divisors of $m$ counted with
multiplicity.) What about $<\epsilon \log\log m$?

Barreto and Leeham, using ChatGPT and Aristotle, have proved a negative answer, which was
quantified by Tao and Alexeev (see the comments).
-/
@[category research solved, AMS 11]
theorem erdos_205.parts.ii : answer(False) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      IsRepresentable (fun m => ε * Real.log (Real.log m)) n := by
  sorry

/--
Is it true that all sufficiently large $n$ can be written as $2^k+m$ for some $k\geq 0$, where
$\Omega(m)<\log\log m$? (Here $\Omega(m)$ is the number of prime divisors of $m$ counted with
multiplicity.) Or some more slowly growing function?

Barreto and Leeham, using ChatGPT and Aristotle, have proved a negative answer, which was
quantified by Tao and Alexeev (see the comments).
-/
@[category research solved, AMS 11]
theorem erdos_205.parts.iii : answer(False) ↔
    ∃ f : ℕ → ℝ, f =o[atTop] (fun m : ℕ => Real.log (Real.log m)) ∧
      ∀ᶠ n : ℕ in atTop, IsRepresentable f n := by
  sorry

/--
In fact there are infinitely many $n$ such that, for all $k$ with $2^k<n$, $n-2^k$ has at least
\[\gg \left(\frac{\log n}{\log\log n}\right)^{1/2}\]
many prime factors.
-/
@[category research solved, AMS 11]
theorem erdos_205.variants.many_prime_factors : ∃ c > (0 : ℝ),
    {n : ℕ | ∀ k : ℕ, 2 ^ k < n →
      c * Real.sqrt (Real.log n / Real.log (Real.log n)) ≤ (Ω (n - 2 ^ k) : ℝ)}.Infinite := by
  sorry

/--
The $n$ constructed in this way are divisible by a large power of $2$. It remains open whether
there exist arbitrarily large odd counterexamples.
-/
@[category research open, AMS 11]
theorem erdos_205.variants.odd_counterexamples : answer(sorry) ↔
    {n : ℕ | Odd n ∧ ¬ IsRepresentable (fun m => Real.log (Real.log m)) n}.Infinite := by
  sorry

end Erdos205
