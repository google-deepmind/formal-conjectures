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
# Erdős Problem 764

*Reference:* [erdosproblems.com/764](https://www.erdosproblems.com/764)

A conjecture of Erdős [Er65b][Er70c] on whether the partial sums of the 3-fold additive
convolution $1_A \ast 1_A \ast 1_A$ can have bounded error term around a linear function.
Related to problem 763, which concerns the 2-fold convolution.

Disproved by Vaughan [Va72], who proved the answer is no in a strong form, showing that even
$\sum_{n \leq N} 1_A \ast 1_A \ast 1_A(n) = cN + o(N^{1/4} / (\log N)^{1/2})$ is impossible.
-/

open Finset BigOperators Classical

namespace Erdos764

/-- The number of representations of $n$ as $a_1 + a_2 + a_3$ with
$a_1, a_2, a_3 \in A$, i.e., the 3-fold additive convolution
$1_A \ast 1_A \ast 1_A(n)$. -/
noncomputable def repCount764 (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun p => p.1 + p.2 ≤ n ∧ p.1 ∈ A ∧ p.2 ∈ A ∧ (n - p.1 - p.2) ∈ A)).card

/-- The partial sum $\sum_{n=0}^{N} 1_A \ast 1_A \ast 1_A(n)$. -/
noncomputable def repSum764 (A : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).sum (fun n => repCount764 A n)

/--
Erdős Problem 764 (Vaughan's theorem) [Va72]:

There do not exist $A \subseteq \mathbb{N}$ and $c > 0$ such that
$\sum_{n \leq N} 1_A \ast 1_A \ast 1_A(n) = cN + O(1)$.
-/
@[category research solved, AMS 11]
theorem erdos_764 : answer(False) ↔
    ∃ (A : Set ℕ) (c : ℝ), c > 0 ∧
      ∃ C : ℝ, ∀ N : ℕ, |↑(repSum764 A N) - c * ↑N| ≤ C := by
  sorry

end Erdos764
