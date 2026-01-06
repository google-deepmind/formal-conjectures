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

/-- `barrier f n` means `n` is a barrier for the function `f`,
    i.e. `m + f m ≤ n` for all `m < n`. -/
def barrier (f : ℕ → ℕ) (n : ℕ) : Prop := ∀ m < n, m + f m ≤ n

/-- Are there infinitely many barriers for `ω`? -/
@[category research open, AMS 11]
theorem erdos_413 : ({ n | barrier ω n }.Infinite) ↔ answer(sorry) := by
  sorry

/-- `expProd n` is `∏ kᵢ` when `n = ∏ pᵢ ^ kᵢ`, i.e. the product of the prime exponents of `n`. -/
def expProd (n : ℕ) : ℕ :=
  n.factorization.support.prod fun p => n.factorization p

/-- Erdős proved that the barrier set for `expProd` is infinite and even has positive density. -/
@[category research solved, AMS 11]
theorem erdos_413_expProd_barrier_pos_density :
    { n | barrier expProd n }.HasPosDensity := by
  sorry

/-- Erdős believed there should be infinitely many barriers for `Ω`, the total prime multiplicity. -/
@[category research open, AMS 11]
theorem erdos_413_bigOmega :
    ({ n | barrier Ω n }.Infinite) ↔ answer(sorry) := by
  sorry

/-- Selfridge computed that the largest `Ω`-barrier below `10^5` is `99840`. -/
@[category research solved, AMS 11]
theorem erdos_413_bigOmega_largest_barrier_lt_100k :
    IsGreatest {n : ℕ | n < 10 ^ 5 ∧ barrier Ω n} 99840 := by
  sorry

/-- `barrierWith ε f n` records the relaxed barrier inequality `(m : ℝ) + ε * f m ≤ n` for all `m < n`. -/
def barrierWith (ε : ℝ) (f : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ m < n, (m : ℝ) + ε * (f m : ℝ) ≤ (n : ℝ)

/-- Does there exist some `ε > 0` such that there are infinitely many `ε`-barriers for `ω`? -/
@[category research open, AMS 11]
theorem erdos_413_epsilon :
    (∃ ε > (0 : ℝ), { n | barrierWith ε ω n }.Infinite) ↔ answer(sorry) := by
  sorry

end Erdos413
