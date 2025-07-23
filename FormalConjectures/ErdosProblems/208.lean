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
# Erdős Problem 208
*Reference:* [erdosproblems.com/208](https://www.erdosproblems.com/208)
-/

open Filter Real

/-- The sequence of squarefree numbers, denoted by `s` as in Erdős problem 208. -/
noncomputable def erdos208.s : ℕ → ℕ := Nat.nth Squarefree

open erdos208

/--
Let $s_1 < s_2 < ⋯$ be the sequence of squarefree numbers. Is it true that
for any $ϵ > 0$ and large $n$, $s_{n+1} − s_n ≪_ϵ s_n^ε$?
-/
@[category research open, AMS 11]
theorem erdos_208.i :
    (∀ ε > (0 : ℝ), (fun n => (s (n + 1) - s n : ℝ)) =O[atTop] (fun n => (s n : ℝ)^ε)) ↔
    answer(sorry) := by sorry

/--
Let $s_1 < s_2 < ⋯$ be the sequence of squarefree numbers. Is it true that
$s_{n + 1} - s_n ≤ (1 + o(1)) * (\pi^2 / 6) * log (s_n) / log (log (s_n))$?
-/
@[category research open, AMS 11]
theorem erdos_208.ii :
    (∃ (c : ℕ → ℝ), (c =o[atTop] (1 : ℕ → ℝ)) ∧ ∀ᶠ n in atTop,
      s (n + 1) - s n ≤ (1 + (c n)) * (π^2 / 6) * log (s n) / log (log (s n))) ↔ answer(sorry) := by
  sorry

/--
In [Er79] Erdős says perhaps $s_{n+1} − s_n ≪ log s_n$, but he is 'very doubtful'.

[Er79] Erdős, Paul, __Some unconventional problems in number theory__. Math. Mag. (1979), 67-70.
-/
@[category research open, AMS 11]
theorem erdos_208.variants.log_bound :
    (fun n ↦ (s (n + 1) - s n : ℝ)) =O[atTop] fun n ↦ log (s n) := by sorry
