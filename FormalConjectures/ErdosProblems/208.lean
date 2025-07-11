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

-- TODO: Need to fix wording on website...

/--
Let `s1 < s2 < ⋯` be a sequence of squarefree numbers. Is it true that, for any `ϵ > 0` and large `n`,
`s (n+1) − s n ≪_ϵ (s n)^ε`?
-/
theorem erdos_208.i (s : ℕ → ℕ) (hs₀ : StrictMono s) (hs₁ : ∀ n, Squarefree (s n)) :
    ∀ ε > 0, ∃ C > 0, ∀ᶠ n in atTop, s (n + 1) - s n < C * (s n)^ε := sorry

/--
Let `s1 < s2 < ⋯` be a sequence of squarefree numbers. Is it true that
`s (n + 1) - s n ≤ (1 + o(1)) * (π^2 / 6) * log (s n) / log (log (s n))`?
-/
theorem erdos_208.ii (s : ℕ → ℕ) (hs₀ : StrictMono s) (hs₁ : ∀ n, Squarefree (s n)) :
    ∃ (c : ℕ → ℝ), (c =o[atTop] (fun n ↦ (1 : ℝ))) ∧
    ∀ᶠ n in atTop, s (n + 1) - s n ≤ (1 + (c n)) * (π^2 / 6) * log (s n) / log (log (s n))  := sorry

/--
Erdős says perhaps `s (n+1) − s n ≪ log (s n)`, but he is 'very doubtful'.
-/
theorem erdos_208.variants.log_bound (s : ℕ → ℕ) (hs₀ : StrictMono s) (hs₁ : ∀ n, Squarefree (s n)) :
    (fun n ↦ (s (n + 1) - s n : ℝ)) =O[atTop] fun n ↦ log (s n) := sorry
