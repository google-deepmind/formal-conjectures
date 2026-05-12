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

/-!
# Catalan's Mersenne Conjecture

*References:*
- [Wikipedia - Catalan's Mersenne conjecture](https://en.wikipedia.org/wiki/Catalan%27s_Mersenne_conjecture)
- [OEIS A007013](https://oeis.org/A007013)
-/

namespace CatalanMersenne

/-- Catalan-Mersenne sequence: c₀=2, c_{n+1}=2^{cₙ}-1.
    Known values: 2, 3, 7, 127, 2^127-1. All known terms are prime. -/
def catalanMersenne : ℕ → ℕ
  | 0     => 2
  | n + 1 => 2 ^ catalanMersenne n - 1

/-- **Catalan's Mersenne Conjecture**: every term of the Catalan-Mersenne sequence is prime.
    Verified for n ≤ 4; unknown for n ≥ 5. -/
@[category research open, AMS 11]
theorem catalan_mersenne_prime : ∀ n, (catalanMersenne n).Prime := by
  sorry


end CatalanMersenne
