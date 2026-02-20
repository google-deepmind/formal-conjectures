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
- [A5236](https://oeis.org/A5236)

Erdős called a natural number `n` a *barrier* for `ω`, the number of distinct prime divisors,
if `m + ω(m) ≤ n` for all `m < n`. He believed there should be infinitely many such barriers, and
even posed a relaxed variant asking whether there is some `ε > 0` for which infinitely many `n`
satisfy `m + ε · ω(m) ≤ n` for every `m < n`.
-/

open ArithmeticFunction
open scoped omega Omega

namespace Erdos413

/-- `IsBarrier f n` means `n` is a barrier for the real-valued function `f`,
i.e. `(m : ℝ) + f m ≤ (n : ℝ)` for all `m < n`. -/
def IsBarrier (f : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ m < n, (m : ℝ) + f m ≤ n

/-- Are there infinitely many barriers for `ω`? -/
@[category research open, AMS 11]
theorem erdos_413 :
    answer(sorry) ↔ { n | IsBarrier (fun m => ω m) n }.Infinite := by
  sorry

/-- `expProd n` is `∏ kᵢ` when `n = ∏ pᵢ ^ kᵢ`, i.e. the product of the prime exponents of `n`. -/
def expProd (n : ℕ) : ℕ :=
  n.factorization.prod fun _ e => e

/-- Erdős proved that the barrier set for `expProd` is infinite and even has positive density. -/
@[category research solved, AMS 11]
theorem erdos_413_hasPosDensity_barrier_expProd :
    { n | IsBarrier (fun m => expProd m) n }.HasPosDensity := by
  sorry

/-- Erdős believed there should be infinitely many barriers for `Ω`, the total prime multiplicity. -/
@[category research open, AMS 11]
theorem erdos_413_bigOmega :
    answer(sorry) ↔ { n | IsBarrier (fun m => Ω m) n }.Infinite := by
  sorry

/-- Selfridge computed that the largest `Ω`-barrier below `10^5` is `99840`. -/
@[category research solved, AMS 11]
theorem erdos_413_bigOmega_largest_barrier_lt_100k :
    IsGreatest {n : ℕ | n < 10 ^ 5 ∧ IsBarrier (fun m => Ω m) n} 99840 := by
  sorry

/-- Does there exist some `ε > 0` such that there are infinitely many `ε`-barriers for `ω`? -/
@[category research open, AMS 11]
theorem erdos_413_epsilon :
    answer(sorry) ↔
        (∃ ε > (0 : ℝ), { n | IsBarrier (fun n => ε * ω n) n }.Infinite) := by
  sorry

end Erdos413
