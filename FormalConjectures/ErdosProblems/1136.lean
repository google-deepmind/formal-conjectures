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
import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 1136

*Reference:* [erdosproblems.com/1136](https://www.erdosproblems.com/1136)

Does there exist $A \subseteq \mathbb{N}$ with lower density $> 1/3$ such that $a + b \neq 2^k$
for any $a, b \in A$ and $k \geq 0$?

A question asked by Erdős at the DMV conference in Berlin 1987. Achieving density $1/3$ is trivial,
taking $A$ to be all multiples of $3$.

Müller [Mu11] settled this question in the affirmative: one can take $A$ to be the set of all
integers congruent to $3 \cdot 2^i \pmod{2^{i+2}}$ for any $i \geq 0$, which has density $1/2$.
Müller also proved this is best possible, in that such $A$ has lower density at most $1/2$.

[Mu11] Müller, H., *Über ein additiv-zahlentheoretisches Problem von P. Erdős*.
Mitteilungen der Mathematischen Gesellschaft in Hamburg (2011), 75–78.
-/

open Classical

namespace Erdos1136

/-- A set $A \subseteq \mathbb{N}$ is power-of-2 sum-free if no two elements (not necessarily
    distinct) sum to a power of $2$. -/
def PowerOfTwoSumFree (A : Set ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → ∀ k : ℕ, a + b ≠ 2 ^ k

/--
Erdős Problem 1136 (Proved by Müller [Mu11]):
There exists $A \subseteq \mathbb{N}$ with lower density strictly greater than $1/3$ such that
no two elements of $A$ sum to a power of $2$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1136 : answer(True) ↔
    ∃ (A : Set ℕ),
      PowerOfTwoSumFree A ∧
      1/3 < Set.lowerDensity A := by
  sorry

/--
Müller's explicit construction [Mu11]: the set of all integers congruent to $3 \cdot 2^i
\pmod{2^{i+2}}$ for some $i \geq 0$ is power-of-2 sum-free and has density $1/2$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1136_construction :
    let A := {n : ℕ | ∃ i : ℕ, n % 2 ^ (i + 2) = 3 * 2 ^ i}
    PowerOfTwoSumFree A ∧
    Set.lowerDensity A = 1/2 := by
  sorry

/--
Müller's optimality result [Mu11]: no power-of-2 sum-free set can have lower density
exceeding $1/2$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1136_upper :
    ∀ A : Set ℕ, PowerOfTwoSumFree A → Set.lowerDensity A ≤ 1/2 := by
  sorry

end Erdos1136
