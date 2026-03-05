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
# Erdős Problem 246

*Reference:* [erdosproblems.com/246](https://www.erdosproblems.com/246)

Let $a, b \geq 2$ with $\gcd(a, b) = 1$. Then the set of all numbers of the form
$a^k \cdot b^\ell$ (with $k, \ell \geq 0$) is complete: every sufficiently large positive
integer can be written as a sum of distinct elements of this set.

[Bi59] Birch, B. J., *Note on a problem of Erdős*.

[Ca60] Cassels, J. W. S.

[Er61] Erdős, P.

[He00b] Hegyvári, N.
-/

namespace Erdos246

/-- The set of all natural numbers of the form $a^k \cdot b^\ell$ for $k, \ell \geq 0$. -/
def twoPowerSet (a b : ℕ) : Set ℕ :=
  {n : ℕ | ∃ k l : ℕ, n = a ^ k * b ^ l}

/-- A set $S \subseteq \mathbb{N}$ is complete if every sufficiently large natural number
can be expressed as a sum of distinct elements of $S$. -/
def IsComplete (S : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N < n →
    ∃ F : Finset ℕ, (↑F ⊆ S) ∧ ∑ x ∈ F, x = n

/--
Erdős Problem 246 [Er61] (proved by Birch [Bi59]):
Let $a, b \geq 2$ with $\gcd(a, b) = 1$. Then every sufficiently large positive integer
is the sum of distinct integers of the form $a^k \cdot b^\ell$ with $k, \ell \geq 0$.

This also follows from a later more general result of Cassels [Ca60] (see Problem 254).
-/
@[category research solved, AMS 5 11]
theorem erdos_246 :
    ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → Nat.Coprime a b →
      IsComplete (twoPowerSet a b) := by
  sorry

end Erdos246
