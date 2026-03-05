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
# Erdős Problem 658

Is it true that if $A \subseteq \{1, \ldots, N\}^2$ has $|A| \geq \delta N^2$ then $A$ must
contain the vertices of an axis-aligned square? This was proved via the density Hales–Jewett
theorem by Furstenberg and Katznelson, with a quantitative proof given by Solymosi.

*Reference:* [erdosproblems.com/658](https://www.erdosproblems.com/658)
-/

open Finset

namespace Erdos658

/--
A subset $A$ of $\mathbb{N} \times \mathbb{N}$ contains the vertices of an axis-aligned square
if there exist $a, b, d$ with $d \geq 1$ such that all four corners
$(a, b)$, $(a + d, b)$, $(a, b + d)$, $(a + d, b + d)$ lie in $A$.
-/
def ContainsAxisAlignedSquare (A : Finset (ℕ × ℕ)) : Prop :=
  ∃ a b d : ℕ, d ≥ 1 ∧
    (a, b) ∈ A ∧ (a + d, b) ∈ A ∧ (a, b + d) ∈ A ∧ (a + d, b + d) ∈ A

/--
For any $\delta > 0$, for all sufficiently large $N$, if $A \subseteq \{1, \ldots, N\}^2$ has
$|A| \geq \delta N^2$ then $A$ must contain the vertices of an axis-aligned square.

This is a problem originally attributed to Graham. The qualitative statement
follows from the density Hales-Jewett theorem proved by Furstenberg and Katznelson.
A quantitative proof was given by Solymosi.
-/
@[category research solved, AMS 5]
theorem erdos_658 : answer(True) ↔
    (∀ δ : ℝ, δ > 0 →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ A : Finset (ℕ × ℕ),
          A ⊆ Finset.Icc 1 N ×ˢ Finset.Icc 1 N →
          (A.card : ℝ) ≥ δ * (N : ℝ) ^ 2 →
          ContainsAxisAlignedSquare A) := by
  sorry

end Erdos658
