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
# Erdős Problem 656

*Reference:* [erdosproblems.com/656](https://www.erdosproblems.com/656)

Let $A \subseteq \mathbb{N}$ have positive upper density. Must there exist an infinite set
$B \subseteq \mathbb{N}$ and an integer $t$ such that $B + B + t \subseteq A$?
Solved affirmatively by Kra, Moreira, Richter, and Robertson [KMRR24].

[Er75b] Erdős, P., *Problems and results on combinatorial number theory III*, 1975.

[KMRR24] Kra, B., Moreira, J., Richter, F., and Robertson, D., 2024.
-/

open Filter

namespace Erdos656

/-- The upper density of a set $A \subseteq \mathbb{N}$, defined as
$\limsup_{N \to \infty} |A \cap \{0, \ldots, N-1\}| / N$. -/
noncomputable def Nat.upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ =>
    ((@Finset.filter _ (· ∈ A) (Classical.decPred (· ∈ A)) (Finset.range N)).card : ℝ) / N) atTop

/--
**Erdős Problem 656** [Er75b]:

Let $A \subseteq \mathbb{N}$ have positive upper density. Then there exist an infinite set
$B \subseteq \mathbb{N}$ and an integer $t$ such that $b_1 + b_2 + t \in A$ for all
$b_1, b_2 \in B$ (where the arithmetic is in $\mathbb{Z}$).

Proved by Kra, Moreira, Richter, and Robertson [KMRR24].
-/
@[category research solved, AMS 5 11]
theorem erdos_656 : answer(True) ↔
    ∀ (A : Set ℕ), Nat.upperDensity A > 0 →
      ∃ (B : Set ℕ) (t : ℤ), Set.Infinite B ∧
        ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∃ a ∈ A, (a : ℤ) = ↑b₁ + ↑b₂ + t := by
  sorry

end Erdos656
