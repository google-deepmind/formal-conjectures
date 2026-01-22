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

import FormalConjectures.Util.ProblemImports

/-! # Woodall Primes

References:
* [Wikipedia/Woodall Number](https://en.wikipedia.org/wiki/Woodall_number#Woodall_primes)
* [OEIS/A002234](https://oeis.org/A002234)

-/

namespace WoodallPrimes

/-- There are infinitely many prime numbers of the form `k * 2 ^ k - 1` for `k > 1`. -/
@[category research open, AMS 11]
theorem infinitely_many_woodall_primes : {k : ℕ | 1 < k ∧ (k * 2 ^ k - 1).Prime}.Infinite := by
  sorry

end WoodallPrimes
