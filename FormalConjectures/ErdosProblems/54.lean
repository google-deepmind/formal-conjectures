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
# Erdős Problem 54

*Reference:* [erdosproblems.com/54](https://www.erdosproblems.com/54)

There exists a Ramsey 2-complete set $A$ (every large integer is a monochromatic subset sum
under any 2-colouring) with $|A \cap \{1,\ldots,N\}| \leq c (\log N)^2$.
Resolved by Conlon, Fox, and Pham [CFP21].

See also Problems 55 and 843.

[BuEr85] Burr, S. A. and Erdős, P., _On the completeness of sequences of sums of powers
of integers_ (1985).
[Er95] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
[CFP21] Conlon, D., Fox, J., and Pham, H.T., _Subset sums, completeness and colorings_ (2021).
-/

open scoped Classical
open Finset Real

namespace Erdos54

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
Erdős Problem 54 (resolved by Conlon, Fox, and Pham [CFP21]):
There exists a Ramsey 2-complete set $A$ of positive integers and a constant $c > 0$
such that $|A \cap \{1, \ldots, N\}| \leq c \cdot (\log N)^2$ for all sufficiently large $N$.

This improves the upper bound $(2 \log_2 N)^3$ of Burr and Erdős [BuEr85], matching the
lower bound order of $(\log N)^2$.
-/
@[category research solved, AMS 5 11]
theorem erdos_54 :
    ∃ (A : Set ℕ),
      IsRamseyComplete A 2 ∧
        ∃ c : ℝ, c > 0 ∧
          ∃ N₀ : ℕ, ∀ N ≥ N₀,
            (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) ≤
              c * (Real.log (N : ℝ)) ^ 2 := by
  sorry

/--
Lower bound (Burr–Erdős [BuEr85]): there exists $c > 0$ such that any set $A$ with
$|A \cap \{1, \ldots, N\}| \leq c \cdot (\log N)^2$ for all large $N$ cannot be
Ramsey 2-complete. Together with `erdos_54`, this shows the optimal growth rate
is $\Theta((\log N)^2)$.
-/
@[category research solved, AMS 5 11]
theorem erdos_54.variants.lower_bound :
    ∃ c : ℝ, c > 0 ∧
      ∀ (A : Set ℕ),
        (∃ N₀ : ℕ, ∀ N ≥ N₀,
          (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) ≤
            c * (Real.log (N : ℝ)) ^ 2) →
        ¬ IsRamseyComplete A 2 := by
  sorry

end Erdos54
