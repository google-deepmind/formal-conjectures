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
# Erdős Problem 723

Also known as the prime power conjecture.

*Reference:* [erdosproblems.com/723](https://www.erdosproblems.com/723)
-/

open Configuration

namespace Erdos723

variable {P L : Type} [Membership P L]

/--
If there is a finite projective plane of order $n$ then must $n$ be a prime power?
-/
@[category research open, AMS 5]
theorem erdos_732 : (∀ pp : ProjectivePlane P L, IsPrimePow pp.order) ↔ answer(sorry) := by
  sorry

/--
These always exist if $n$ is a prime power.
-/
@[category research solved, AMS 5]
theorem erdos_732.prime_pow_is_projplane_order :
    ∀ n, IsPrimePow n → ∃ pp : ProjectivePlane P L, pp.order = n := by
  sorry

/--
This conjecture has been proved for $n \leq 11$.
-/
@[category research solved, AMS 5]
theorem erdos_732.leq_11 : ∀ pp : ProjectivePlane P L, pp.order ≤ 11 → IsPrimePow pp.order := by
  sorry

/--
It is open whether there exists a projective plane of order 12.
-/
@[category research open, AMS 5]
theorem erdos_732.eq_12 : (∃ pp : ProjectivePlane P L, pp.order = 12) ↔ answer(sorry) :=  by
  sorry

/--
Bruck and Ryser have proved that if $n \equiv 1 (\mod 4)$ or $n \equiv 2 (\mod 4)$ then $n$ must be
the sum of two squares.
-/
@[category research solved, AMS 5]
theorem bruck_ryser (n : ℕ) (pp : ProjectivePlane P L) (hpp : pp.order = n) :
    (n ≡ 1 [MOD 4] ∨ n ≡ 2 [MOD 4]) → ∃ a b, n = a ^ 2 + b ^ 2 := by
  sorry

end Erdos723
