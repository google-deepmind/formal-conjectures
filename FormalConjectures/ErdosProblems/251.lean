/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 251

*Reference:* [erdosproblems.com/251](https://www.erdosproblems.com/251)
-/

namespace Erdos251

/--
Is $\sum_{n=1}^\infty \frac{p_n}{2^n}$ irrational? Here $p_n$ is the $n$-th prime ($p_1=2, p_2=3, \dots$).
-/
@[category research open, AMS 11]
theorem erdos_251 : answer(sorry) ↔ Irrational (∑' n : ℕ, (Nat.nth Nat.Prime n) / (2 ^ n)) := by
  sorry

/--
Summation by parts relates the series in `erdos_251` to the corresponding
series of consecutive prime gaps:
$$ \sum_{n \ge 0} \frac{p_n}{2^n} = 4 + \sum_{n \ge 0} \frac{p_{n+1} - p_n}{2^n}. $$
The constant is $4$ rather than $2$ because `erdos_251` is indexed from
$n = 0$, so its first term is $p_0/2^0 = 2$ and the whole series is twice the
classical one-based one.

This is an exact reformulation of the series in `erdos_251`; it does not prove
that either series is irrational.
-/
@[category textbook, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-lean-erdos249-257/blob/ceaee37f2df872af9e19c90f2b88d87f06fec85d/adapters/FormalConjecturesVariants.lean#L392-L412"]
theorem erdos_251.variants.prime_gap_identity :
    (∑' n : ℕ, (Nat.nth Nat.Prime n : ℝ) / (2 ^ n)) =
      4 + ∑' n : ℕ, (primeGap n : ℝ) / (2 ^ n) := by
  sorry

/--
Irrationality of the prime dyadic series in `erdos_251` is equivalent to
irrationality of the corresponding consecutive-prime-gap dyadic series.

The equivalence is hypothesis-free: convergence of both series is established
in the linked proof from the elementary bound $p_n \le 1250(n+1)^4$, so no
summability premise appears.

This is an exact reformulation, not a proof of the irrationality of either
series, so `erdos_251` remains open.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-lean-erdos249-257/blob/ceaee37f2df872af9e19c90f2b88d87f06fec85d/adapters/FormalConjecturesVariants.lean#L417-L421"]
theorem erdos_251.variants.prime_gap_transfer :
    Irrational (∑' n : ℕ, (Nat.nth Nat.Prime n : ℝ) / (2 ^ n)) ↔
      Irrational (∑' n : ℕ, (primeGap n : ℝ) / (2 ^ n)) := by
  sorry

end Erdos251
