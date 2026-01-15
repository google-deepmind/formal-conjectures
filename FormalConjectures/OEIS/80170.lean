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

import FormalConjectures.Util.ProblemImports
import Mathlib.Algebra.IsPrimePow

/-!
# Conjecture relating two characterizations of a set of integers.

Informal Statement:
For an integer $k ≥ 2$, the following are equivalent:

1. The greatest common divisor of the binomial coefficients
    $\binom{2k}{k}, \binom{3k}{k}, \dots, \binom{(k+1)k}{k} = 1$.

2. Writing prime factorization of k as
    $k = \prod p_i^{e_i}$, and let
    $P = \max_i p_i^{e_i}$,
    one has $k / P > P$.

This conjecture asserts that the integers satisfying (1)
are exactly those satisfying (2).

*Reference:*
- [A080170](https://oeis.org/A080170)
- [A051283](https://oeis.org/A051283)
-/

namespace OeisA080170

/--
The gcd of the binomial coefficients
$\binom{2k}{k}, \binom{3k}{k}, \dots, \binom{(k+1)k}{k} = 1$.
-/
def GCDCondition (k : ℕ) : Prop :=
  (Finset.range k).gcd (fun i => Nat.choose ((i + 2) * k) k) = 1

/--
Let P be the largest prime power dividing `k`.
Then $k / P > P$.
-/
def PrimePowerCondition (k : ℕ) : Prop :=
  let P := ((Nat.divisors k).filter IsPrimePow).max.getD 0
  k / P > P

/--
Conjecture: The gcd condition is equivalent to the prime power condition.
-/
@[category research open, AMS 11]
theorem gcdCondition_iff_primePowerCondition (k : ℕ) (hk : 2 ≤ k) :
    GCDCondition k ↔ PrimePowerCondition k := by
  sorry

end OeisA080170
