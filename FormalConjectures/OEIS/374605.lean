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
# Sum of products $\binom{n}{k}^2 \binom{n+k}{k} \binom{3n+2k}{n}$

The sequence is defined by
$$a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k} \binom{3n+2k}{n}$$

*References:*
- [A374605](https://oeis.org/A374605)
-/

open Nat Finset

namespace OeisA374605

/--
The sequence $a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k} \binom{3n+2k}{n}$.
-/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1),
    (choose n k) ^ 2 * (choose (n + k) k) * (choose (3 * n + 2 * k) n)

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := rfl
@[category test, AMS 11]
theorem a_1 : a 1 = 13 := by rfl
@[category test, AMS 11]
theorem a_2 : a 2 = 621 := by rfl
@[category test, AMS 11]
theorem a_3 : a 3 = 40864 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 3116125 := by rfl

/--
Conjecture: for prime $p \ge 5$, $a(n)$ is divisible by $p^3$ for integer $n$ in the interval
$[\lceil\frac{2p + 1}{3}\rceil, p - 1]$.
The lower bound $\lceil\frac{2p + 1}{3}\rceil$ for $p \in \mathbb{N}$ is expressed using
natural number division as $(2 * p + 1 + 2) / 3 = (2 * p + 3) / 3$.
-/
@[category research open, AMS 11]
theorem supercongruence (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
  ∀ n : ℕ,
    (2 * p + 3) / 3 ≤ n →
    n ≤ p - 1 →
    (p ^ 3 : ℕ) ∣ a n := by sorry

end OeisA374605
