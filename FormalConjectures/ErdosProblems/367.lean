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
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics

/-!
# Erdős Problem 367

*Reference:* [erdosproblems.com/367](https://www.erdosproblems.com/367)

Let $B_2(n)$ be the $2$-full part of $n$ (that is, $B_2(n)=n/n'$ where $n'$ is the
product of all primes that divide $n$ exactly once). Is it true that, for every
fixed $k\geq 1$,
\[
\prod_{n\leq m<n+k}B_2(m) \ll n^{2+o(1)}?
\]
Or perhaps even $\ll_k n^2$?
-/

namespace Erdos367

open Finset Real Asymptotics

/--
The `2`-full part of a natural number: remove all prime factors that occur exactly once.
-/
noncomputable def B2 (n : ℕ) : ℕ :=
  let factors := n.factors -- multiset of prime factors
  let single_primes := { p : ℕ | p.Prime ∧ n.factorization p = 1 } -- primes appearing exactly once
  let n' := ∏ p in single_primes, p -- product of those primes
  n / n' -- remove them from n

/--
The product of `B2(m)` for `m = n, n+1, ..., n+k-1`.
-/
noncomputable def productB2 (k n : ℕ) : ℕ :=
  ∏ i in Finset.range k, B2 (n + i)

/--
Weak conjecture: For every fixed `ε > 0`, the product is `O(n^{2+ε})`.
-/
@[category research open, AMS 52]
theorem erdos_367_weak (k : ℕ) (hk : k ≥ 1) :
    ∀ ε > 0, ∃ C : ℝ, ∀ n ≥ 1, (productB2 k n : ℝ) ≤ C * (n : ℝ) ^ (2 + ε) := by
  sorry

/--
Strong conjecture: For every fixed `k`, the product is `O_k(n^2)`.
-/
@[category research open, AMS 52]
theorem erdos_367_strong (k : ℕ) (hk : k ≥ 1) :
    ∃ C : ℝ, ∀ n ≥ 1, (productB2 k n : ℝ) ≤ C * (n : ℝ) ^ 2 := by
  sorry

end Erdos367
