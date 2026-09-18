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
# Least $m > 0$ coprime to $n$ such that $mn \mid C(m+n)$

The sequence $a(n)$ is the least positive integer $m$ such that $\gcd(m, n) = 1$ and
$m \cdot n \mid C(m+n)$, where $C(k) = \frac{1}{k+1} \binom{2k}{k}$ is the $k$-th Catalan number.

*References:*
- [A248123](https://oeis.org/A248123)
-/

namespace OeisA248123

open Nat Set

/-- The $k$-th Catalan number $C(k) = \frac{1}{k+1} \binom{2k}{k}$. -/
def catalan (k : ℕ) : ℕ := (2 * k).choose k / (k + 1)

/-- The primary sequence $a(n)$: least integer $m > 0$ such that $\gcd(m, n) = 1$ and
$m \cdot n \mid C(m+n)$, where $C(k)$ is the $k$-th Catalan number. Returns $0$ if no such $m$
exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | 0 < m ∧ Nat.gcd m n = 1 ∧ (m * n) ∣ catalan (m + n) }

macro "eval_a" : tactic => `(tactic| {
  dsimp [a]
  apply IsLeast.csInf_eq
  refine ⟨by decide, fun m hm => ?_⟩
  by_contra! h
  revert hm
  interval_cases m <;> decide
})

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by eval_a

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by eval_a

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by eval_a

@[category test, AMS 11]
theorem a_4 : a 4 = 21 := by eval_a

@[category test, AMS 11]
theorem a_5 : a 5 = 9 := by eval_a

/-- Conjecture: $a(n)$ exists for all $n > 0$.
Since $a(n)$ is defined as the infimum of a set of positive integers, existence is equivalent
to $0 < a(n)$. -/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 0 < n) : 0 < a n := by
  sorry

end OeisA248123
