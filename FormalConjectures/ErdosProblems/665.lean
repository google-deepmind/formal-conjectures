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
# Erdős Problem 665

*Reference:* [erdosproblems.com/665](https://www.erdosproblems.com/665)

A pairwise balanced design for $\{1, \ldots, n\}$ is a collection of sets
$A_1, \ldots, A_m \subseteq \{1, \ldots, n\}$ such that $2 \leq |A_i| < n$ and every pair
of distinct elements $x, y \in \{1, \ldots, n\}$ is contained in exactly one $A_i$.

[ErLa82] Erdős, P. and Larson, J. A., 1982.

[ShSi85] Shrikhande, S. S. and Singhi, N. M., 1985.

[Er97f] Erdős, P., 1997.
-/

open Finset

namespace Erdos665

/-- A pairwise balanced design on `Fin n`: a family of blocks where each block has
at least $2$ and fewer than $n$ elements, and every pair of distinct elements is
contained in exactly one block. -/
def IsPairwiseBalancedDesign (n : ℕ) (blocks : Finset (Finset (Fin n))) : Prop :=
  (∀ B ∈ blocks, 2 ≤ B.card ∧ B.card < n) ∧
  (∀ x y : Fin n, x ≠ y → ∃! B, B ∈ blocks ∧ x ∈ B ∧ y ∈ B)

/--
Erdős Problem 665 [ErLa82][Er97f]:

Is there a constant $C > 0$ such that for all sufficiently large $n$, there exists
a pairwise balanced design on $\{1, \ldots, n\}$ where every block has size
$> \sqrt{n} - C$?

Shrikhande and Singhi [ShSi85] proved that the answer is no conditional on the
conjecture that the order of every projective plane is a prime power.
-/
@[category research open, AMS 5]
theorem erdos_665 : answer(sorry) ↔
    ∃ C : ℝ, C > 0 ∧
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    ∃ blocks : Finset (Finset (Fin n)),
      IsPairwiseBalancedDesign n blocks ∧
      ∀ B ∈ blocks, (↑B.card : ℝ) > Real.sqrt ↑n - C := by
  sorry

end Erdos665
