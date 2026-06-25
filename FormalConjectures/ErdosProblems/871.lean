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
# Erdős Problem 871

*Reference:* [erdosproblems.com/871](https://www.erdosproblems.com/871)
-/

namespace Erdos871

/--
Let $A$ be an additive basis of order $2$, and suppose $1_A\ast 1_A(n)\to \infty$ as $n\to \infty$. Can $A$ be partitioned into two disjoint additive bases of order $2$?
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos871.lean"]
theorem erdos_871 :
    answer(False) ↔
      ∀ (A : Set ℕ),
        (∀ᶠ n in Filter.atTop, ∃ a ∈ A, ∃ b ∈ A, a + b = n) ∧
        (∀ t, ∀ᶠ n in Filter.atTop, ∃ pairs : Finset (ℕ × ℕ),
          pairs.card ≥ t ∧
            ∀ p ∈ pairs, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2) →
        ∃ (B C : Set ℕ),
          (∀ x, x ∈ A ↔ x ∈ B ∨ x ∈ C) ∧
          Disjoint B C ∧
          (∀ᶠ n in Filter.atTop, ∃ a ∈ B, ∃ b ∈ B, a + b = n) ∧
          (∀ᶠ n in Filter.atTop, ∃ a ∈ C, ∃ b ∈ C, a + b = n) := by
  sorry

end Erdos871
