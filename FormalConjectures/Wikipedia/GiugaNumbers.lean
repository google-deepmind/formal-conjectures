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

/-
# Giuga Numbers

*References:*
- [Wikipedia] (https://en.wikipedia.org/wiki/Giuga_number)
- [A007850] (https://oeis.org/A007850)
-/

namespace GiugaNumbers

/-
Given n ∈ ℕ, n is a Giuga Number if it is a composite number
such that for each prime divisor p of n, p divides ((n / p) - 1)
-/
def is_giuga_number (n : ℕ) : Prop :=
  n.Composite ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ∣ (n / p - 1)

/-
The Infinite Giuga Number Conjecture asks if there exists
infinitely many Giuga Numbers
-/
@[category research open, AMS 11]
theorem infinite_giuga_number :
  Set.Infinite {n : ℕ | is_giuga_number n} := by
  sorry

namespace GiugaNumbers
