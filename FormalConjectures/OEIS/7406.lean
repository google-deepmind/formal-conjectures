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
import FormalConjectures.OEIS.«89026»

/-!
# Wolstenholme numbers

Wolstenholme numbers: numerator of $\sum_{k=1}^n \frac{1}{k^2}$.

*References:*
- [A007406](https://oeis.org/A007406)
-/

namespace OeisA7406

/-- Wolstenholme numbers: numerator of $\sum_{k=1}^n \frac{1}{k^2}$. -/
def a (n : ℕ) : ℕ :=
  (∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ) ^ 2).num.natAbs

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by decide +native

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide +native

@[category test, AMS 11]
theorem a_2 : a 2 = 5 := by decide +native

@[category test, AMS 11]
theorem a_3 : a 3 = 49 := by decide +native

@[category test, AMS 11]
theorem a_4 : a 4 = 205 := by decide +native

/--
Conjecture: for $n > 3$, $\gcd(n, a(n-1)) = \text{A089026}(n)$.
- Amiram Eldar and Thomas Ordowski, Jul 28 2019
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 3 < n) :
    Nat.gcd n (a (n - 1)) = OeisA89026.a n := by
  sorry

end OeisA7406
