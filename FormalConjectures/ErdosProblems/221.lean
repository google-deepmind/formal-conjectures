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
# Erdős Problem 221

Is there a set $A \subseteq \mathbb{N}$ with $|A \cap \{1, \ldots, N\}| \ll N / \log N$
such that every sufficiently large integer can be written as $2^k + a$ for some
$k \geq 0$ and $a \in A$?

*Reference:* [erdosproblems.com/221](https://www.erdosproblems.com/221)
-/

open scoped Classical
open Finset Real

namespace Erdos221

/--
Is there a set $A \subseteq \mathbb{N}$ such that
$|A \cap \{1, \ldots, N\}| \ll N / \log N$ and every sufficiently large integer can be
written as $2^k + a$ for some $k \geq 0$ and $a \in A$?

The answer is yes, proved by Ruzsa (1972).
-/
@[category research solved, AMS 11]
theorem erdos_221 :
    answer(True) ↔
      ∃ (A : Set ℕ),
        (∃ (C : ℝ), C > 0 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) ≤ C * ↑N / Real.log ↑N) ∧
        (∃ M : ℕ, ∀ n : ℕ, M ≤ n → ∃ k : ℕ, ∃ a ∈ A, n = 2 ^ k + a) := by
  sorry

end Erdos221
