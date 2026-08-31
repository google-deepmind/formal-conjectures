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
# Erdős Problem 431

*References:*
- [erdosproblems.com/431](https://www.erdosproblems.com/431)
- [El01] Elsholtz, Christian, *The inverse Goldbach problem*. Mathematika (2001), 151-158.
- [ElHa15] Elsholtz, Christian and Harper, Adam J., *Additive decompositions of sets with restricted
  prime factors*. Trans. Amer. Math. Soc. (2015), 7403-7427.
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [Gr90] Granville, Andrew, *A note on sums of primes*. Canad. Math. Bull. (1990), 452--454.
- [TaZi23] Tao, Terence and Ziegler, Tamar, *Infinite partial sumsets in the primes*. J. Anal. Math.
  (2023), 375--389.

Note: following Ostmann's definition of asymptotic additive decomposability (quoted in [ElHa15]),
`A` and `B` are required to be sets of positive integers.
-/

open scoped Pointwise

namespace Erdos431

/--
Are there two infinite sets $A$ and $B$ such that $A+B$ agrees with the set of prime numbers up to finitely many exceptions?
-/
@[category research open, AMS 11]
theorem erdos_431 : answer(sorry) ↔
    ∃ A B : Set ℕ, 0 ∉ A ∧ 0 ∉ B ∧ A.Infinite ∧ B.Infinite ∧
      (symmDiff (A + B) {p : ℕ | p.Prime}).Finite := by
  sorry

end Erdos431
