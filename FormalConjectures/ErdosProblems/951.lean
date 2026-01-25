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
# Erdős Problem 951

*Reference:*
 - [erdosproblems.com/951](https://www.erdosproblems.com/951)
 - [Er77c] Erdős, Paul, Problems and results on combinatorial number theory. III. Number theory day (Proc. Conf., Rockefeller Univ.,
    New York, 1976) (1977), 43-72.
-/

open scoped Finsupp Nat.Prime
open Filter

/-- A sequence of real numbers `1 < a 0 < a 1 < ...` is called a set of Beurling prime numbers if
it tends to infinity. -/
noncomputable def IsBeurlingPrimes (a : ℕ → ℝ) : Prop :=
  1 < a 0 ∧ StrictMono a ∧ Tendsto a atTop atTop

/-- The set of Beurling integers are numbers of the form `∏ i, (a i) ^ (k i)`, where `k` has
finite support. -/
def BeurlingInteger (a : ℕ → ℝ) : Set ℝ :=
  let g : (ℕ →₀ ℕ) → ℝ := fun k => k.prod (fun x y => (a x) ^ y)
  .range g

namespace Erdos951

/-- A sequence `a : ℕ → ℝ` is said to have property `Erdos951` if for any pair of distinct
Beuring integers `x, y`, `|x - y| ≥ 1`. -/
def Erdos951 (a : ℕ → ℝ) : Prop :=
  ∀ x y : ℝ, x ≠ y → x ∈ BeurlingInteger a → y ∈ BeurlingInteger a → |x - y| ≥ 1

/-- If `a` has property `Erdos951` and `1 < a 0`, then `a` is a set of Beurling prime numbers. -/
@[category API, AMS 11]
theorem erdos_951.isBeurlingPrimes {a : ℕ → ℝ} (ha : 1 < a 0):
    IsBeurlingPrimes a := by
  sorry

/-- If `a` has property `Erdos951`, is it true that `#{a i ≤ x} ≤ π x`? -/
@[category research open, AMS 11]
theorem erdos_951 : answer(sorry) ↔
    ∀ a : ℕ → ℝ, Erdos951 a → ∀ (x : ℝ), {i : ℕ | a i ≤ x}.ncard ≤ π ⌊x⌋₊ := by
  sorry

/-- Beurling conjectured that if the number of Beurling integer in `[1, x]`
is `x + o(log x)`, then `a` must be the sequence of primes. -/
@[category research solved, AMS 11]
theorem erdos_951.Beurling : answer(sorry) ↔
    ∀ a : ℕ → ℝ, IsBeurlingPrimes a →
    ((fun x => (BeurlingInteger a ∩ .Iic x).ncard - x) =o[atTop] Real.log) →
    ∀ i, a i = Nat.nth Nat.Prime i  := by
  sorry

end Erdos951
