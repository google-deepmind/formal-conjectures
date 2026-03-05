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

[CFP21] Conlon, D., Fox, J., and Pham, H.T., _Subset sums, completeness and colorings_. (2021).
-/

open scoped Classical
open Finset Real

namespace Erdos54

/--
A set $A$ of natural numbers is Ramsey 2-complete if for every 2-coloring of $\mathbb{N}$,
all sufficiently large natural numbers can be represented as a sum of distinct
elements of $A$ that all receive the same color.
-/
def IsRamsey2Complete (A : Set ℕ) : Prop :=
  ∀ (χ : ℕ → Fin 2),
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∃ (S : Finset ℕ), (↑S : Set ℕ) ⊆ A ∧
        (∃ c : Fin 2, ∀ x ∈ S, χ x = c) ∧
        S.sum id = n

/--
Erdős Problem 54 (resolved by Conlon, Fox, and Pham [CFP21]):
There exists a Ramsey 2-complete set $A$ of positive integers and a constant $c > 0$
such that $|A \cap \{1, \ldots, N\}| \leq c \cdot (\log N)^2$ for all sufficiently large $N$.

This improves the upper bound $(2 \log_2 N)^3$ of Burr and Erdős, matching the
lower bound order of $(\log N)^2$.
-/
@[category research solved, AMS 5]
theorem erdos_54 :
    ∃ (A : Set ℕ),
      IsRamsey2Complete A ∧
        ∃ c : ℝ, c > 0 ∧
          ∃ N₀ : ℕ, ∀ N ≥ N₀,
            (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) ≤
              c * (Real.log (N : ℝ)) ^ 2 := by
  sorry

end Erdos54
