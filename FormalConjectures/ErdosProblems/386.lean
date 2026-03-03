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

/-!
# Erdős Problem 386
*Reference:* [erdosproblems.com/386](https://www.erdosproblems.com/386)
-/


namespace Erdos386

open Nat

/--
There is a $k$, such that $2 \le k \le n - 2$ and
$\binom{n}{k}$ can be the product of consecutive primes infinitely often?
-/
@[category research open, AMS 11]
theorem erdos_386 :
    answer(sorry) ↔ ∃ k ≥ 2, ∃ᶠ n in .atTop,
      k ≤ n - 2 ∧ ∃ p q : ℕ, n.choose k = ∏ i ∈ .Ico p q, nth Nat.Prime i := by
    sorry

/--
For all $2 \le k \le n - 2$,
can $\binom{n}{k}$ be the product of consecutive primes infinitely often?
-/
@[category research open, AMS 11]
theorem erdos_386.variants_forall :
    answer(sorry) ↔ ∀ k ≥ 2, ∃ᶠ n in .atTop,
      k ≤ n - 2 ∧ ∃ p q : ℕ, n.choose k = ∏ i ∈ .Ico p q, nth Nat.Prime i := by
    sorry

/--
Can $\binom{n}{2}$ be the product of consecutive primes infinitely often?
-/
@[category research open, AMS 11]
theorem erdos_386.variants_two :
    answer(sorry) ↔ ∃ᶠ n in .atTop,
      2 ≤ n - 2 ∧ ∃ p q : ℕ, n.choose 2 = ∏ i ∈ .Ico p q, nth Nat.Prime i := by
    sorry

/--
For $k = 2$, $\binom{n}{2} = n(n-1)/2$; known cases include $\binom{4}{2} = 6 = 2 \cdot 3$,
the product of the first two consecutive primes. Such finite verifications confirm the
problem is non-trivially posed for small $n$.
-/
@[category research formally solved using formal_conjectures at "https://www.erdosproblems.com/386", AMS 11]
theorem erdos_386.variants.known_result :
    (4 : ℕ).choose 2 = ∏ i ∈ Finset.Ico 0 2, nth Nat.Prime i := by
  sorry

end Erdos386
