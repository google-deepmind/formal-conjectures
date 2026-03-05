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
# Erdős Problem 806

Must every set $A \subseteq \{1, \ldots, n\}$ with $|A| \leq \sqrt{n}$ be contained in
$B + B$ for some $B \subset \mathbb{Z}$ with $|B| = o(\sqrt{n})$?

*Reference:* [erdosproblems.com/806](https://www.erdosproblems.com/806)

[ErNe77] Erdős, P. and Newman, D.J., *Bases for sets of integers*, J. Number Theory (1977).

[ABS09] Alon, N., Bukh, B., and Sudakov, B., *Discrete Kakeya-type problems and small bases for
the integers*, Israel J. Math. (2009).
-/

namespace Erdos806

/--
Erdős Problem 806 [ErNe77]:

For any $\varepsilon > 0$, for all sufficiently large $n$, for any $A \subseteq \{1, \ldots, n\}$
with $|A| \leq \sqrt{n}$, there exists a finite set $B \subset \mathbb{Z}$ with
$|B| \leq \varepsilon \cdot \sqrt{n}$ such that every element of $A$ (viewed in $\mathbb{Z}$)
belongs to $B + B$.

This captures the $o(\sqrt{n})$ conjecture. It was resolved by Alon, Bukh, and
Sudakov [ABS09] with the sharper bound $|B| \leq C \cdot (\log \log n / \log n) \cdot \sqrt{n}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_806 : answer(True) ↔
    ∀ (ε : ℝ), 0 < ε →
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∀ A : Finset ℕ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) → (A.card : ℝ) ≤ Real.sqrt n →
    ∃ B : Finset ℤ, (B.card : ℝ) ≤ ε * Real.sqrt n ∧
      ∀ a ∈ A, ∃ b₁ ∈ B, ∃ b₂ ∈ B, (a : ℤ) = b₁ + b₂ := by
  sorry

end Erdos806
