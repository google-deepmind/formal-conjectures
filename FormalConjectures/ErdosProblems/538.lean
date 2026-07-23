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
# Erdős Problem 538

*Reference:* [erdosproblems.com/538](https://www.erdosproblems.com/538)

Let `r ≥ 2` and suppose `A ⊆ {1, ..., N}` is such that, for any `m`, there are
at most `r` solutions to `m = p a` with `p` prime and `a ∈ A`.  Give the best
possible upper bound for `∑_{n ∈ A} 1 / n`.
-/

noncomputable section

namespace Erdos538

open Classical
open scoped BigOperators

/-- The number of prime-multiple representations `m = p a` with `a ∈ A`. -/
def primeMultipleRepresentationCount (A : Finset ℕ) (m : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 2 m).filter fun p =>
    Nat.Prime p ∧ ∃ a : ℕ, a ∈ A ∧ m = p * a).card

/-- The representation multiplicity hypothesis from the problem. -/
def PrimeMultipleMultiplicityAtMost (r N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    ∀ m : ℕ, primeMultipleRepresentationCount A m ≤ r

/-- The reciprocal sum of a finite set of positive integers. -/
def reciprocalSum (A : Finset ℕ) : ℝ :=
  A.sum fun n => (1 : ℝ) / (n : ℝ)

/-- `B r N` is the best possible upper bound for the reciprocal sum. -/
def BestReciprocalSumUpperBound (B : ℕ → ℕ → ℝ) : Prop :=
  ∀ r N : ℕ,
    2 ≤ r →
      IsLeast
        {C : ℝ |
          ∀ A : Finset ℕ,
            PrimeMultipleMultiplicityAtMost r N A → reciprocalSum A ≤ C}
        (B r N)

/--
Determine the best possible upper bound for the reciprocal sum under the
prime-multiple representation multiplicity condition.
-/
@[category research open, AMS 11]
theorem erdos_538 :
    {B : ℕ → ℕ → ℝ | BestReciprocalSumUpperBound B} = answer(sorry) := by
  sorry

end Erdos538

end
