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
import FormalConjecturesForMathlib.Combinatorics.Additive.Convolution

/-!
# Erdős Problem 763

*Reference:* [erdosproblems.com/763](https://www.erdosproblems.com/763)

Let $A \subseteq \mathbb{N}$. Can there exist some constant $c > 0$ such that
$$\sum_{n \leq N} 1_A \ast 1_A(n) = cN + O(1)?$$
Here $1_A \ast 1_A(n)$ denotes the number of representations of $n$ as $a + b$
with $a, b \in A$.

A conjecture of Erdős and Turán [Er65b][Er70c].

Disproved: Erdős and Fuchs [ErFu56] proved the answer is no in a strong
form: even $\sum_{n \leq N} 1_A \ast 1_A(n) = cN + o(N^{1/4} / (\log N)^{1/2})$
is impossible. The error term was later improved to $o(N^{1/4})$ by
Jurkat (unpublished) and Montgomery–Vaughan [MoVa90].
-/

open Finset BigOperators Classical AdditiveCombinatorics

namespace Erdos763

/-- The partial sum $\sum_{n=0}^{N} 1_A \ast 1_A(n)$. -/
noncomputable def repSum (A : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).sum (fun n => sumRep A n)

/--
Erdős Problem 763 (Erdős–Fuchs theorem) [ErFu56]:

For any $A \subseteq \mathbb{N}$ and any $c > 0$, the partial sums
$\sum_{n \leq N} 1_A \ast 1_A(n)$ cannot satisfy
$\sum_{n \leq N} 1_A \ast 1_A(n) = cN + O(1)$. That is, the error
term $|\sum_{n \leq N} 1_A \ast 1_A(n) - cN|$ is unbounded.
-/
@[category research solved, AMS 11]
theorem erdos_763 : answer(False) ↔
    ∃ (A : Set ℕ) (c : ℝ), c > 0 ∧
      ∃ C : ℝ, ∀ N : ℕ, |↑(repSum A N) - c * ↑N| ≤ C := by
  sorry

end Erdos763
