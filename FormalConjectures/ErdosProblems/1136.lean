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

import FormalConjecturesUtil

/-!
# Erdős Problem 1136

*References:*
- [erdosproblems.com/1136](https://www.erdosproblems.com/1136)
- [Mu11] Müller, Helmut, *Über ein additiv-zahlentheoretisches Problem von P. Erdős*.
  Mitt. Math. Ges. Hamburg (2011), 75-78.
-/

namespace Erdos1136

/--
A set `A` of natural numbers has the property in the question if `a + b ≠ 2 ^ k` for all
`a, b ∈ A` (not necessarily distinct) and all `k ≥ 0`.
-/
def AvoidsPowersOfTwo (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ k : ℕ, a + b ≠ 2 ^ k

/-- The set of all integers congruent to $3\cdot 2^i\pmod{2^{i+2}}$ for some $i\geq 0$. -/
def muellerSet : Set ℕ := {n | ∃ i : ℕ, n ≡ 3 * 2 ^ i [MOD 2 ^ (i + 2)]}

/--
Does there exist $A\subset \mathbb{N}$ with lower density $>1/3$ such that $a+b\neq 2^k$ for
any $a,b\in A$ and $k\geq 0$?

Müller [Mu11] settled this question in the affirmative: in fact one can take $A$ to be
the set of all integers congruent to $3\cdot 2^i\pmod{2^{i+2}}$ for any $i\geq 0$, which has
density $1/2$.
-/
@[category research solved, AMS 11]
theorem erdos_1136 : answer(True) ↔
    ∃ A : Set ℕ, (1 / 3 : ℝ) < A.lowerDensity ∧ AvoidsPowersOfTwo A := by
  sorry

/--
Achieving density $1/3$ is trivial, taking $A$ to be all multiples of $3$.
-/
@[category research solved, AMS 11]
theorem erdos_1136.variants.multiples_of_three :
    AvoidsPowersOfTwo {n : ℕ | 3 ∣ n} ∧ Set.HasDensity {n : ℕ | 3 ∣ n} (1 / 3) := by
  sorry

/--
Müller [Mu11] settled this question in the affirmative: in fact one can take $A$ to be
the set of all integers congruent to $3\cdot 2^i\pmod{2^{i+2}}$ for any $i\geq 0$, which has
density $1/2$.
-/
@[category research solved, AMS 11]
theorem erdos_1136.variants.mueller :
    AvoidsPowersOfTwo muellerSet ∧ muellerSet.HasDensity (1 / 2) := by
  sorry

/--
Müller also proved this is best possible, in that $A$ with the property in the question has
lower density at most $1/2$.
-/
@[category research solved, AMS 11]
theorem erdos_1136.variants.upper_bound (A : Set ℕ) (hA : AvoidsPowersOfTwo A) :
    A.lowerDensity ≤ 1 / 2 := by
  sorry

end Erdos1136
