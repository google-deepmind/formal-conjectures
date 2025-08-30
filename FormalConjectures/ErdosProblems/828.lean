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
# Erdős Problem 828

*Reference:* [erdosproblems.com/828](https://www.erdosproblems.com/828)
-/

namespace Erdos828

open scoped Nat

/--
Is it true that, for any $a \in \mathbb{Z}$, there are infinitely many $n$ such that
$$\phi(n) | n + a$$?
-/
@[category research open, AMS 11]
theorem erdos_828 : (∀ a : ℤ, Set.Infinite {n : ℕ | ↑(φ n) ∣ n + a}) ↔ answer(sorry) := by
  sorry

/--
When $n > 1$, Lehmer conjectured that $\phi(n) | n - 1$ if and only if $n$ is prime.
-/
@[category research open, AMS 11]
theorem erdos_828.variants.lehmer_conjecture : (∀ n > 1, φ n ∣ n - 1 ↔ Prime n) ↔ answer(sorry) := by
  sorry

/--
It is an easy exercise to show that, for $n > 1$, $\phi(n) | n$ if and only if $n = 2^a 3^b$.
-/
@[category undergraduate, AMS 11]
theorem erdos_828.variants.phi_dvd_self_iff_pow2_pow3 : ∀ n > 1, φ n ∣ n ↔ ∃ a b, n = 2^a * 3^b := by
  sorry

end Erdos828
