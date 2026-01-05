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
# Erdős Problem 413

*References:*
- [erdosproblems.com/413](https://www.erdosproblems.com/413)
- [OEIS A005236](https://oeis.org/A005236)

Erdős called a natural number `n` a *barrier* for `ω`, the number of distinct prime divisors,
if `m + ω(m) ≤ n` for all `m < n`. He believed there should be infinitely many such barriers, and
even posed a relaxed variant asking whether there is some `ε > 0` for which infinitely many `n`
satisfy `m + ε · ω(m) ≤ n` for every `m < n`.
-/

open scoped ArithmeticFunction

namespace Erdos413

/-- `barrier n` means `n` is an Erdős barrier for `ω`, i.e. `m + ω(m) ≤ n` for all `m < n`. -/
def barrier (n : ℕ) : Prop := ∀ m < n, m + ω m ≤ n

/-- Are there infinitely many barriers for `ω`? -/
@[category research open, AMS 11]
theorem erdos_413 : ({ n | barrier n }.Infinite) ↔ answer(sorry) := by
  sorry

/-- `barrierWith ε n` records the relaxed barrier inequality `(m : ℝ) + ε * ω(m) ≤ n` for all `m < n`. -/
def barrierWith (ε : ℝ) (n : ℕ) : Prop :=
  ∀ m < n, (m : ℝ) + ε * (ω m : ℝ) ≤ (n : ℝ)

/-- Does there exist some `ε > 0` such that there are infinitely many `ε`-barriers for `ω`? -/
@[category research open, AMS 11]
theorem erdos_413_epsilon :
    (∃ ε > (0 : ℝ), { n | barrierWith ε n }.Infinite) ↔ answer(sorry) := by
  sorry

end Erdos413
