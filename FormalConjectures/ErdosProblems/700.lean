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
# Erdős Problem 700

*Reference:* [erdosproblems.com/700](https://www.erdosproblems.com/700)

For composite `n`, let
`f(n) = min_{1 < k ≤ n/2} gcd(n, Nat.choose n k)`.
The page asks:

* characterize composite `n` for which `f(n) = n / P(n)`, where `P(n)` is the
  largest prime factor of `n`;
* whether infinitely many composite `n` satisfy `f(n) > n^(1/2)`;
* whether, for every `A > 0`, `f(n) ≪_A n / (log n)^A` for all composite `n`.
-/

noncomputable section

namespace Erdos700

open Classical Filter

/-- `n` is composite. -/
def Composite (n : ℕ) : Prop :=
  1 < n ∧ ¬ Nat.Prime n

/-- `f` is the minimum of `gcd(n, Nat.choose n k)` over `1 < k ≤ n / 2`. -/
def IsBinomialGcdMinimum (n f : ℕ) : Prop :=
  IsLeast
    {g : ℕ |
      ∃ k : ℕ,
        1 < k ∧
          k ≤ n / 2 ∧
            g = Nat.gcd n (Nat.choose n k)}
    f

/-- `p` is the largest prime factor of `n`. -/
def IsLargestPrimeFactor (n p : ℕ) : Prop :=
  Nat.Prime p ∧ p ∣ n ∧ ∀ q : ℕ, Nat.Prime q → q ∣ n → q ≤ p

/-- A proposed characterization of the composite `n` with `f(n) = n / P(n)`. -/
def CharacterizesEqualityWithLargestPrimeFactorQuotient (C : ℕ → Prop) : Prop :=
  ∀ n : ℕ,
    Composite n →
      (C n ↔
        ∃ f p : ℕ,
          IsBinomialGcdMinimum n f ∧
            IsLargestPrimeFactor n p ∧
              f = n / p)

/-- Infinitely many composite `n` satisfy `f(n) > sqrt n`. -/
def Erdos700LargeBinomialGcdInfinitelyOften : Prop :=
  ∀ N : ℕ,
    ∃ n f : ℕ,
      N ≤ n ∧
        Composite n ∧
          IsBinomialGcdMinimum n f ∧
            Real.sqrt (n : ℝ) < (f : ℝ)

/-- For every `A > 0`, the bound `f(n) ≪_A n / (log n)^A` holds for composites. -/
def Erdos700LogPowerBound : Prop :=
  ∀ A : ℝ,
    0 < A →
      ∃ C : ℝ,
        0 < C ∧
          ∀ᶠ n in atTop,
            Composite n →
              ∃ f : ℕ,
                IsBinomialGcdMinimum n f ∧
                  (f : ℝ) ≤
                    C * (n : ℝ) / Real.rpow (Real.log (n : ℝ)) A

/-- Characterize the composites for which `f(n) = n / P(n)`. -/
@[category research open, AMS 11]
theorem erdos_700.parts.i :
    {C : ℕ → Prop | CharacterizesEqualityWithLargestPrimeFactorQuotient C} =
      answer(sorry) := by
  sorry

/-- Are there infinitely many composite `n` with `f(n) > sqrt n`? -/
@[category research open, AMS 11]
theorem erdos_700.parts.ii :
    answer(sorry) ↔ Erdos700LargeBinomialGcdInfinitelyOften := by
  sorry

/-- Is `f(n) ≪_A n / (log n)^A` for every `A > 0` on the composite integers? -/
@[category research open, AMS 11]
theorem erdos_700.parts.iii : answer(sorry) ↔ Erdos700LogPowerBound := by
  sorry

end Erdos700

end
