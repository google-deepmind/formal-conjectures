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

namespace Erdos784

/--
`HarmonicBound A C n` means:  
A ⊆ {1,…,n} and ∑_{a ∈ A} (1/a) ≤ C.
We keep this as an abstract predicate.
-/
def HarmonicBound (A : Set ℕ) (C : ℝ) (n : ℕ) : Prop := False

/--
`AvoidsAllDivisors m A` means:  
For every a ∈ A, a ∤ m.
This models “m avoids divisibility by all elements of A”.
-/
def AvoidsAllDivisors (m : ℕ) (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ¬ a ∣ m

/--
Erdős problem 784:  
If A ⊆ {1,…,n} satisfies ∑ (1/a) ≤ C, must there exist c = c(C)
such that the count of integers ≤ n avoiding divisors from A is at least  
n / (log n)^c, for all sufficiently large n?
-/
@[category research open, AMS 11]
theorem erdos_784 :
    (∀ C > 0,
      ∃ c : ℝ,
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ A : Set ℕ,
            HarmonicBound A C n →
              {m : ℕ | m ≤ n ∧ AvoidsAllDivisors m A}.ncard
                ≥ n / (Real.log n) ^ c) ↔
      answer(sorry) := by
  sorry

end Erdos784

