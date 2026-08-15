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
# Erdős Problem 423

*Reference:* [erdosproblems.com/423](https://www.erdosproblems.com/423)

Let `a₁ = 1` and `a₂ = 2`.  For `k ≥ 3`, choose `a_k` to be the least integer
greater than `a_{k-1}` which is the sum of at least two consecutive earlier
terms of the sequence.  What is the asymptotic behaviour of this sequence?
-/

noncomputable section

namespace Erdos423

open Classical
open scoped BigOperators

/-- Sum of `len` consecutive terms of a sequence, starting at index `start`. -/
def consecutiveBlockSum (a : ℕ → ℕ) (start len : ℕ) : ℕ :=
  (Finset.range len).sum fun j => a (start + j)

/--
`x` is a sum of at least two consecutive terms of `a`, using only terms with
indices `< k`.
-/
def SumOfAtLeastTwoEarlierConsecutiveTerms (a : ℕ → ℕ) (k x : ℕ) : Prop :=
  ∃ start len : ℕ,
    2 ≤ len ∧
      start + len ≤ k ∧
        x = consecutiveBlockSum a start len

/-- The Hofstadter-Erdős sequence described in problem 423, indexed from `0`. -/
def HofstadterErdosSequence (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧
    a 1 = 2 ∧
      ∀ k : ℕ,
        2 ≤ k →
          IsLeast
            {x : ℕ |
              a (k - 1) < x ∧ SumOfAtLeastTwoEarlierConsecutiveTerms a k x}
            (a k)

/--
Determine the asymptotic behaviour of the sequence obtained by repeatedly
taking the least new integer which is a sum of at least two consecutive earlier
terms.
-/
@[category research open, AMS 11]
theorem erdos_423 : {a : ℕ → ℕ | HofstadterErdosSequence a} = answer(sorry) := by
  sorry

end Erdos423

end
