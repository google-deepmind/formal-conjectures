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

open Nat Set

/--
A224515: $a(n) = \text{least } k \text{ such that } \sqrt{k^2 \operatorname{XOR} (k+1)^2} = 2n+1, \text{ } a(n) = -1 \text{ if there is no such } k$.
This is equivalent to finding the smallest $k \in \mathbb{N}$ such that $k^2 \oplus (k+1)^2 = (2n+1)^2$.
We use the set infimum ($\operatorname{sInf}$) to denote the least element of the set of natural numbers satisfying the condition.
Since Mathlib's `sInf` on a subset of `ℕ` gives a result in `ℕ`, this definition is only completely faithful to the OEIS when the set is non-empty.
The OEIS definition implies that the set of k's is non-empty for all n.
-/
noncomputable def A224515 (n : ℕ) : ℕ :=
  -- The term (2*n + 1)^2 is the target value.
  let target_sq : ℕ := (2 * n + 1) ^ 2
  -- Define the set of candidate k's.
  sInf { k : ℕ | Nat.xor (k ^ 2) ((k + 1) ^ 2) = target_sq }

/--
**OEIS A224515 Conjecture 1:** A solution $k$ always exists.
Formalization: For every natural number $n$, there is a $k$ such that $k^2 \oplus (k+1)^2 = (2n+1)^2$.
This ensures that $a(n) \ge 0$ in the context of the OEIS definition, as the set of solutions must be non-empty.
-/
theorem A224515_conjecture_existence (n : ℕ) :
  ∃ k : ℕ, Nat.xor (k ^ 2) ((k + 1) ^ 2) = (2 * n + 1) ^ 2 := by
  sorry

/--
**OEIS A224515 Conjecture 2:** The least $k$ is also the only such $k$.
Formalization: For every natural number $n$, the set of solutions for $k$ is a singleton (i.e., has at most one element).
-/
theorem A224515_conjecture_uniqueness (n : ℕ) :
  ∀ k₁ k₂ : ℕ,
    (Nat.xor (k₁ ^ 2) ((k₁ + 1) ^ 2) = (2 * n + 1) ^ 2) ∧
    (Nat.xor (k₂ ^ 2) ((k₂ + 1) ^ 2) = (2 * n + 1) ^ 2) →
    k₁ = k₂ := by
  sorry
