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
# Erdős Problem 452

*Reference:* [erdosproblems.com/452](https://www.erdosproblems.com/452)

Let `ω(n)` count the number of distinct prime factors of `n`.  What is the
size of the largest interval `I ⊆ [x, 2x]` such that
`ω(n) > log log n` for all `n ∈ I`?
-/

noncomputable section

namespace Erdos452

open Classical

/-- The number of distinct prime factors of `n`. -/
def omega (n : ℕ) : ℕ :=
  ((Finset.Icc 2 n).filter fun p => Nat.Prime p ∧ p ∣ n).card

/-- A consecutive interval of length `len`, beginning at `start`, lies in `[x,2x]`. -/
def IntervalContainedInDyadicSegment (x start len : ℕ) : Prop :=
  x ≤ start ∧ start + len ≤ 2 * x + 1

/-- Every integer in the interval has `ω(n) > log log n`. -/
def IntervalHasLargeOmega (start len : ℕ) : Prop :=
  ∀ n : ℕ,
    n ∈ Finset.Icc start (start + len - 1) →
      Real.log (Real.log (n : ℝ)) < (omega n : ℝ)

/-- `L` is the largest possible length of such an interval inside `[x,2x]`. -/
def IsLargestLargeOmegaIntervalLength (x L : ℕ) : Prop :=
  IsGreatest
    {len : ℕ |
      ∃ start : ℕ,
        IntervalContainedInDyadicSegment x start len ∧
          IntervalHasLargeOmega start len}
    L

/-- A function giving the extremal interval length for every `x`. -/
def LargeOmegaIntervalLengthFunction (L : ℕ → ℕ) : Prop :=
  ∀ x : ℕ, IsLargestLargeOmegaIntervalLength x (L x)

/-- Determine the largest length of an interval in `[x,2x]` with `ω(n) > log log n`. -/
@[category research open, AMS 11]
theorem erdos_452 :
    {L : ℕ → ℕ | LargeOmegaIntervalLengthFunction L} = answer(sorry) := by
  sorry

end Erdos452

end
