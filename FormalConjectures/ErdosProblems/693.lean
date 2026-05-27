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
# Erdős Problem 693

*Reference:* [erdosproblems.com/693](https://www.erdosproblems.com/693)

Let `k ≥ 2` and let `n` be sufficiently large depending on `k`.  Let `A` be
the set of integers in `[n, n^k]` which have a divisor in `(n, 2n)`.  The
problem asks for the maximum gap between consecutive elements of `A`, and in
particular whether it is bounded by a power of `log n`.
-/

noncomputable section

namespace Erdos693

open Classical Filter

/-- `x` has a divisor in the open interval `(n, 2n)`. -/
def HasDivisorInWindow (n x : ℕ) : Prop :=
  ∃ d : ℕ, n < d ∧ d < 2 * n ∧ d ∣ x

/-- The finite set `A ⊂ [n, n^k]` from Erdős problem 693. -/
def divisorWindowSet (k n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc n (n ^ k)).filter fun x => HasDivisorInWindow n x

/-- `x` and `y` are consecutive elements of a finite set of naturals. -/
def ConsecutiveIn (A : Finset ℕ) (x y : ℕ) : Prop :=
  x ∈ A ∧ y ∈ A ∧ x < y ∧
    ∀ z : ℕ, z ∈ A → x < z → z < y → False

/-- The maximum gap in the finite set `A` is at most `B`. -/
def MaxGapAtMost (A : Finset ℕ) (B : ℝ) : Prop :=
  ∀ x y : ℕ, ConsecutiveIn A x y → (y - x : ℝ) ≤ B

/--
The question whether the maximum gap is at most a fixed power of `log n`,
where the exponent may depend on `k`.
-/
def Erdos693PolylogGapConjecture : Prop :=
  ∀ k : ℕ,
    2 ≤ k →
      ∃ C : ℕ,
        ∀ᶠ n in atTop,
          MaxGapAtMost (divisorWindowSet k n) ((Real.log (n : ℝ)) ^ C)

/--
Is the maximum gap between consecutive elements of `A` at most
`(log n) ^ O(1)`?
-/
@[category research open, AMS 11]
theorem erdos_693 : answer(sorry) ↔ Erdos693PolylogGapConjecture := by
  sorry

end Erdos693

end

