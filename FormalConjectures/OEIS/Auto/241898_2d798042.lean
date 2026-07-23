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

open List Nat Finset Classical WithBot

/--
A241898: $a(n)$ is the largest integer such that $n = a(n)^2 + \dots$ is a decomposition of $n$ into a sum of at most four nondecreasing squares.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let P (k : ℕ) : Prop :=
    k > 0 ∧
    ∃ s : List ℕ,
      s.length > 0 ∧ s.length ≤ 4 ∧
      (s.map (fun b => b ^ 2)).sum = n ∧
      s.Sorted (· ≤ ·) ∧
      s.head? = Option.some k -- Qualified 'some' to resolve ambiguity

  -- We explicitly provide the DecidablePred instance using classical logic, which is sound
  -- because the existential quantifier is over a finite, bounded search space.
  have dec : DecidablePred P := fun k => Classical.dec (P k)

  -- Filter the range of possible bases k up to $\lfloor\sqrt{n}\rfloor$.
  let S : Finset ℕ := @Finset.filter _ P dec (range (n.sqrt + 1))

  -- Finset.max returns `WithBot ℕ`. We use `rec 0 id` to convert to `ℕ`,
  -- mapping ⊥ (empty set max) to 0 and a successful max to its value.
  (S.max).rec 0 id


theorem a_one : a 1 = 1 := by
  sorry

theorem a_two : a 2 = 1 := by
  sorry

theorem a_three : a 3 = 1 := by
  sorry

theorem a_four : a 4 = 2 := by
  sorry

/--
From the data that I have, it would seem that a(n) is greater than 7 for all n > 599.
If this could be proved, it would only remain to check if all the numbers up to 599 can be written as the sum of 4 squares none of which is $7^2$.
-/
theorem oeis_241898_conjecture_0 : ∀ n : ℕ, 599 < n → a n > 7 := by
  sorry
