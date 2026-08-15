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

open Finset Nat Real Filter Asymptotics

/--
A051293: Number of nonempty subsets of $\{1, 2, 3, \dots, n\}$ whose elements have an integer average.
-/
def A051293 (n : ℕ) : ℕ :=
  Finset.card (
    (Finset.Icc 1 n).powerset.filter fun S : Finset ℕ =>
      S.Nonempty ∧ S.card ∣ S.sum id
  )

-- Helper function to cast A051293 to a real function of natural numbers.
noncomputable def a_real (n : ℕ) : ℝ := A051293 n

/--
Conjecture (Benoit Cloitre, Oct 20 2002 from OEIS A051293):
a(n) is asymptotic to 2^(n+1)/n. More precisely, I conjecture for any m > 0,
a(n) = 2^(n+1)/n * Sum_{k=0..m} A000670(k)/n^k + o(1/n^(m+1))
(A000670 = preferential arrangements of n labeled elements) which can be written
a(n) = 2^n/n * 2 + Sum_{k=1..m} A000629(k)/n^k + o(1/n^(m+1))
(A000629 = necklaces of sets of labeled beads).
In fact I conjecture that a(n) = 2^(n+1)/n * (1 + 1/n + 3/n^2 + 13/n^3 + 75/n^4 + 541/n^5 + o(1/n^5)).
-/
theorem oeis_51293_conjecture_0 :
    Tendsto
      (fun n : ℕ =>
        -- The numerator f(n)
        (a_real n - ((2 : ℝ) ^ (n + 1) / (n : ℝ)) * (
          (1 : ℝ)
          + 1 / (n : ℝ)
          + 3 / ((n : ℝ) ^ 2)
          + 13 / ((n : ℝ) ^ 3)
          + 75 / ((n : ℝ) ^ 4)
          + 541 / ((n : ℝ) ^ 5)
        ))
        /
        -- The denominator g(n)
        (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))
      )
      atTop
      (nhds 0) := by sorry


-- Example assertions provided in the problem statement, using `decide` where possible.
theorem a_one : A051293 1 = 1 := by
  decide

theorem a_two : A051293 2 = 2 := by
  decide

theorem a_three : A051293 3 = 5 := by
  decide

theorem a_four : A051293 4 = 8 := by
  decide
