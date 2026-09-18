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
# Odd part of the digital sum of $3^n$ divided by the maximal power of $3$

The sequence $a(n)$ is the odd part of the base-$10$ digital sum of $3^n$ divided by the maximal
possible power of $3$.

*References:*
- [A250131](https://oeis.org/A250131)
-/

namespace OeisA250131

open Nat

/-- The primary sequence $a(n)$: the odd part of the digital sum of $3^n$ divided by the maximal
possible power of $3$. -/
def a (n : ℕ) : ℕ :=
  let d := (Nat.digits 10 (3 ^ n)).sum
  let v3 := padicValNat 3 d
  let v2 := padicValNat 2 d
  d / (3 ^ v3 * 2 ^ v2)

/-- Auxiliary sequence $b(n)$ related to A250131: $b(1)=2$, $b(2)=3$, and $b(n)=a(n-2)$ for
$n \ge 3$. -/
def b (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | n' + 3 => a (n' + 1)

/-- The set of indices $n \ge 1$ such that $b(n) \ne 1$ and $b(n)$ is not a multiple of any $b(k)$
for $1 \le k < n$ where $b(k) \ne 1$. This formalizes the Eratosthenes-like sieve applied to $b(n)$
after removing $1$s. -/
def sievedIndices : Set ℕ :=
  { n | 1 ≤ n ∧ b n ≠ 1 ∧ ∀ k, (1 ≤ k ∧ k < n ∧ b k ≠ 1) → ¬ (b k ∣ b n) }

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by native_decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by native_decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by native_decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by native_decide

@[category test, AMS 11]
theorem a_14 : a 14 = 5 := by native_decide

/-- Conjecture: Consider the sequence $b(n)$ such that $b(1)=2$, $b(2)=3$, and for $n \ge 3$,
$b(n)=a(n-2)$. If we apply the Eratosthenes-like sieve to $b(n)$ and remove $1$s, then we obtain a
sequence of primes. -/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : n ∈ sievedIndices) :
    (b n).Prime := by
  sorry

end OeisA250131
