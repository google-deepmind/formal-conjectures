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
# Number of prime powers q<=n such that also q+2 is a prime power

Number of prime powers q<=n such that also q+2 is a prime power.

*References:*
- [A113609](https://oeis.org/A113609)
-/

namespace OeisA113609

/--
A number $n$ is an "OEIS prime power" (for the context of A113609's definition) if $n=1$ or $n$ is a standard prime power.
-/
def is_oeis_prime_power (n : ℕ) : Prop := n = 1 ∨ IsPrimePow n

instance decidable_is_oeis_prime_power (n : ℕ) : Decidable (is_oeis_prime_power n) := by
  simp only [is_oeis_prime_power]
  exact instDecidableOr

/--
The primary defining sequence `a`.
a(n) is the number of prime powers q<=n such that also q+2 is a prime power.
$$a(n) = \operatorname{card} \{q \in \mathbb{N} \mid 1 \le q \le n \land P(q) \land P(q+2) \}$$
-/
def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.range (n + 1)).filter fun q =>
    is_oeis_prime_power q ∧ is_oeis_prime_power (q + 2) ∧ q ≥ 1

/--
(25,27) is the smallest pair of prime powers (q,q+2) such that both q and q+2 are not primes, conjecture: there are more (but not < 10^6).
-/
@[category research open, AMS 11]
theorem main_conjecture :
  answer(sorry) ↔ ∃ q ≥ 1000000,
    is_oeis_prime_power q ∧ is_oeis_prime_power (q + 2) ∧
    ¬ Nat.Prime q ∧ ¬ Nat.Prime (q + 2) := by
  sorry

end OeisA113609
