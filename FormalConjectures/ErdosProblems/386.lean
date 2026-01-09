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
# Erdős Problem 386
*Reference:* [erdosproblems.com/386](https://www.erdosproblems.com/386)
-/


namespace Erdos386

open Nat

/--
Let 2 ≤ k ≤ n − 2. Can binomial(n,k) be the product of consecutive primes infinitely often?
-/
@[category research open, AMS 11]
theorem erdos_386 :
    answer(sorry) ↔ ∀ k \ge 2, ∃\^f n in .atTop,
      k ≤ n - 2 ∧ ∃ p q : ℕ, n.choose k = ∏ i ∈ .Ico p q, nth Nat.Prime i := by
    sorry

end Erdos386
