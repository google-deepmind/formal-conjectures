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
# Alternating sum of binomial coefficient products

$a(1) = 1$, and for $n \ge 2$,
$$a(n) = \sum_{k=0}^{n-2} (-1)^k \binom{n}{k}^2 \binom{n-2}{k}$$

*References:*
- [A361711](https://oeis.org/A361711)
-/
open Nat Int Finset

namespace OeisA361711

/--
$a(1) = 1$, and for $n \ge 2$, $a(n) = \sum_{k=0}^{n-2} (-1)^k \binom{n}{k}^2 \binom{n-2}{k}$.
-/
def a (n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | 1 => 1
  | n_ge_2 =>
    let N := n_ge_2
    -- $n-2$ is the upper limit of summation.
    let m : ℕ := N - 2

    -- The sum is over k from 0 to m, which is range (m + 1).
    ∑ k ∈ range (m + 1),
      let term_nat : ℕ := (N.choose k) * (N.choose k) * (m.choose k)
      let sign_k : ℤ := (-1 : ℤ) ^ k
      sign_k * term_nat.cast

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = -8 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 126 := by rfl

/--
The supercongruence $a(p^k) \equiv a(p^{k-1}) \pmod{p^{3k}}$ holds for all primes $p \ge 5$ and
positive integers $k$.
-/
@[category research open, AMS 11]
theorem conjecture (p : ℕ) (hp : p.Prime) (h_geq_5 : 5 ≤ p) (k : ℕ) (hk : k > 0) :
    a (p ^ k) ≡ a (p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℕ)] := by
  sorry

end OeisA361711
