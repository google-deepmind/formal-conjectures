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
# Erdős Problem 55

*Reference:* [erdosproblems.com/55](https://www.erdosproblems.com/55)

For every $r \geq 2$, there exists an $r$-Ramsey complete set $A$ with
$|A \cap \{1,\ldots,N\}| \leq C \cdot r \cdot (\log N)^2$, and this bound is best possible.
Solved by Conlon, Fox, and Pham [CFP21].

[CFP21] Conlon, D., Fox, J., and Pham, H. T., _The upper bound for Ramsey complete
sequences_, 2021.
-/

open scoped Classical
open Finset Real

namespace Erdos55

/--
A set $A$ of natural numbers is Ramsey $r$-complete if for every $r$-coloring of $\mathbb{N}$,
all sufficiently large natural numbers can be represented as a sum of distinct
elements of $A$ that all receive the same color.
-/
def IsRamseyComplete (A : Set ℕ) (r : ℕ) : Prop :=
  ∀ (χ : ℕ → Fin r),
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∃ (S : Finset ℕ), (↑S : Set ℕ) ⊆ A ∧
        (∃ c : Fin r, ∀ x ∈ S, χ x = c) ∧
        S.sum id = n

/--
Erdős Problem 55 (solved by Conlon, Fox, and Pham [CFP21]):
For every $r \geq 2$, there exists an $r$-Ramsey complete set $A$ such that
$|A \cap \{1, \ldots, N\}| \leq C \cdot r \cdot (\log N)^2$ for all sufficiently large $N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_55 :
    ∀ r : ℕ, 2 ≤ r →
      ∃ (A : Set ℕ),
        IsRamseyComplete A r ∧
          ∃ C : ℝ, C > 0 ∧
            ∃ N₀ : ℕ, ∀ N ≥ N₀,
              (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) ≤
                C * (r : ℝ) * (Real.log (N : ℝ)) ^ 2 := by
  sorry

/--
There exists $c > 0$ such that any set $A$ with
$|A \cap \{1, \ldots, N\}| \leq c \cdot r \cdot (\log N)^2$ for all large $N$
cannot be $r$-Ramsey complete, showing the upper bound is best possible [CFP21].
-/
@[category research solved, AMS 5 11]
theorem erdos_55.variants.lower_bound :
    ∀ r : ℕ, 2 ≤ r →
      ∃ c : ℝ, c > 0 ∧
        ∀ (A : Set ℕ),
          (∃ N₀ : ℕ, ∀ N ≥ N₀,
            (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) ≤
              c * (r : ℝ) * (Real.log (N : ℝ)) ^ 2) →
          ¬ IsRamseyComplete A r := by
  sorry

end Erdos55
