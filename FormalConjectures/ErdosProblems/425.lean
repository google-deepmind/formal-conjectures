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
# Erdős Problem 425

*Reference:* [erdosproblems.com/425](https://www.erdosproblems.com/425)

Let `F(n)` be the maximum size of a subset `A ⊆ {1, ..., n}` such that the
products `ab` are distinct for all `a < b` in `A`.  Is
`F(n) = π(n) + (c + o(1)) n^(3/4) (log n)^(-3/2)` for some constant `c`?

The page also asks an `r`-fold variant: if all products `a₁⋯a_r` are distinct
for `a₁ < ⋯ < a_r`, must `|A| ≤ π(n) + O(n^((r+1)/(2r)))`?
-/

noncomputable section

namespace Erdos425

open Classical Filter
open scoped Topology
open scoped BigOperators

/-- The primes up to `n`, used as a local prime-counting function. -/
def primesUpTo (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter Nat.Prime

/-- A local version of the prime counting function `π(n)`. -/
def primeCounting (n : ℕ) : ℕ :=
  (primesUpTo n).card

/-- The pairwise-products condition: products `ab` with `a < b` are distinct. -/
def PairProductDistinct (A : Finset ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A →
      b ∈ A →
        c ∈ A →
          d ∈ A →
            a < b →
              c < d →
                a * b = c * d → a = c ∧ b = d

/-- `m` is the extremal value `F(n)` from the first part of the problem. -/
def IsPairProductExtremalValue (n m : ℕ) : Prop :=
  IsGreatest
    {s : ℕ |
      ∃ A : Finset ℕ,
        A ⊆ Finset.Icc 1 n ∧ PairProductDistinct A ∧ A.card = s}
    m

/-- A chosen extremal function for the pair-product problem. -/
def PairProductExtremalFunction (F : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, IsPairProductExtremalValue n (F n)

/-- The asymptotic formula conjectured for `F(n)`. -/
def Erdos425MainAsymptotic (F : ℕ → ℕ) : Prop :=
  PairProductExtremalFunction F ∧
    ∃ c : ℝ,
      Tendsto
        (fun n : ℕ =>
          ((F n : ℝ) - (primeCounting n : ℝ)) /
            (Real.rpow (n : ℝ) ((3 : ℝ) / 4) *
              Real.rpow (Real.log (n : ℝ)) (-(3 : ℝ) / 2)))
        atTop
        (𝓝 c)

/--
For `r`, all products over `r` distinct elements of `A` are distinct.  We use
finite subsets of `A` of cardinality exactly `r`.
-/
def RProductsDistinct (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ ⦃S T : Finset ℕ⦄,
    S ⊆ A →
      T ⊆ A →
        S.card = r →
          T.card = r →
            (S.prod fun x => x) = (T.prod fun x => x) → S = T

/-- The `r`-fold upper-bound question from the page. -/
def Erdos425RFoldUpperBound : Prop :=
  ∀ r : ℕ,
    1 ≤ r →
      ∃ C : ℝ,
        0 < C ∧
          ∀ᶠ n in atTop,
            ∀ A : Finset ℕ,
              A ⊆ Finset.Icc 1 n →
                RProductsDistinct r A →
                  (A.card : ℝ) ≤
                    (primeCounting n : ℝ) +
                      C * Real.rpow (n : ℝ) (((r : ℝ) + 1) / (2 * (r : ℝ)))

/--
Main question: determine whether the pair-product extremal function has the
stated second-order asymptotic.
-/
@[category research open, AMS 11 5]
theorem erdos_425.parts.i : {F : ℕ → ℕ | Erdos425MainAsymptotic F} = answer(sorry) := by
  sorry

/-- The `r`-fold product upper-bound variant. -/
@[category research open, AMS 11 5]
theorem erdos_425.parts.ii : answer(sorry) ↔ Erdos425RFoldUpperBound := by
  sorry

end Erdos425

end
