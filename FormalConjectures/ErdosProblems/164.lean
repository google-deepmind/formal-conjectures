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
# Erdős Problem 164

*Reference:* [erdosproblems.com/164](https://www.erdosproblems.com/164)

[Er35] Erdős, P., *Note on sequences of integers no one of which is divisible by any other*.
J. London Math. Soc. (1935).

[Er76g] Erdős, P., *Problems and results on combinatorial number theory* (1976).

[Er86] Erdős, P., *Some problems and results on combinatorial number theory* (1986).

[Li23] Lichtman, J.D., *The Erdős primitive set conjecture*. Forum Math. Pi (2023).
-/

open Real

namespace Erdos164

/-- A set $A$ of natural numbers is primitive (an antichain under divisibility)
if no element divides a distinct element: for all $a, b \in A$, $a \mid b \implies a = b$. -/
def IsPrimitive (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b

/--
Erdős Conjecture (Problem 164) [Er76g, Er86]:

For any primitive set $A \subseteq \{2, 3, 4, \ldots\}$ of natural numbers,
$$\sum_{n \in A} \frac{1}{n \cdot \log n} \leq \sum_{p \text{ prime}} \frac{1}{p \cdot \log p}.$$

That is, the sum $\sum \frac{1}{n \log n}$ over any primitive set is maximised when
the set is the set of all primes.

Proved by Lichtman [Li23].
-/
@[category research solved, AMS 11]
theorem erdos_164 :
    ∀ A : Set ℕ, IsPrimitive A → A ⊆ {n : ℕ | 2 ≤ n} →
    ∑' n : A, (1 : ℝ) / (((n : ℕ) : ℝ) * Real.log ((n : ℕ) : ℝ)) ≤
    ∑' p : {p : ℕ | Nat.Prime p}, (1 : ℝ) / (((p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ)) := by
  sorry

end Erdos164
