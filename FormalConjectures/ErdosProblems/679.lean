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
# Erdős Problem 679

*Reference:* [erdosproblems.com/679](https://www.erdosproblems.com/679)

Let `ω(n)` count the number of distinct prime factors of `n`.  Given
`ε > 0`, are there infinitely many `n` such that
`ω(n-k) < (1+ε) log k / log log k` for all `k < n` which are sufficiently
large depending only on `ε`?
-/

noncomputable section

namespace Erdos679

open Classical

/-- The number of distinct prime factors of `n`. -/
def omega (n : ℕ) : ℕ :=
  ((Finset.Icc 2 n).filter fun p => Nat.Prime p ∧ p ∣ n).card

/--
For a fixed `ε`, `n` has the desired property above the threshold `K`.
The threshold is allowed to depend on `ε`, but not on `n`.
-/
def GoodShiftBoundForEpsilon (ε : ℝ) (K n : ℕ) : Prop :=
  ∀ k : ℕ,
    K ≤ k →
      k < n →
        (omega (n - k) : ℝ) <
          (1 + ε) * Real.log (k : ℝ) / Real.log (Real.log (k : ℝ))

/-- The infinitude question from Erdős problem 679. -/
def Erdos679Conjecture : Prop :=
  ∀ ε : ℝ,
    0 < ε →
      ∃ K : ℕ,
        ∀ N : ℕ,
          ∃ n : ℕ,
            N ≤ n ∧ GoodShiftBoundForEpsilon ε K n

/--
Are there infinitely many `n` for which all sufficiently large shifts `k < n`
have `ω(n-k)` below `(1+ε) log k / log log k`?
-/
@[category research open, AMS 11]
theorem erdos_679 : answer(sorry) ↔ Erdos679Conjecture := by
  sorry

end Erdos679

end
