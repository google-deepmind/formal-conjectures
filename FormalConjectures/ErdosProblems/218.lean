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
# Erdős Problem 218

*Reference:* [erdosproblems.com/218](https://www.erdosproblems.com/218)
-/

namespace Erdos218

/--
The prime gap: the difference between the $n+1$-th and $n$-th prime.
-/
noncomputable def primeGap (n : ℕ) : ℕ := (n + 1).nth Nat.Prime - n.nth Nat.Prime

/--
The set of indices $n$ for which a prime gap is followed by a larger or equal prime gap has a
natural density of $\frac 1 2$.
-/
@[category research open, AMS 11]
theorem erdos_218.variants.le : {n | primeGap n ≤ primeGap (n + 1)}.HasDensity <| 1 / 2 := by
  sorry

/--
The set of indices $n$ for which a prime gap is preceeded by a larger or equal prime gap has a
natural density of $\frac 1 2$.
-/
@[category research open, AMS 11]
theorem erdos_218.variants.ge : {n | primeGap (n + 1) ≤ primeGap n}.HasDensity <| 1 / 2 := by
  sorry

/--
There are infintely many indices $n$ such that the prime gap at $n$ is equal to the prime gap
at $n+1$. This is equivalent to the existence of infinitely many arithmetic progressions of
length $3$, see `erdos_141.variant.infinite_three`.
-/
@[category research open, AMS 11]
theorem erdos_218.variants.infinite_equal_prime_gap : {n | primeGap n = primeGap (n + 1)}.Infinite := by
  sorry

end Erdos218
