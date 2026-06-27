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
# Erdős Problem 199

*References:*
- [erdosproblems.com/199](https://www.erdosproblems.com/199)
- [Ba75] Baumgartner, James E., *Partitioning vector spaces*. J. Combinatorial Theory
  Ser. A (1975), 231-233.
-/

namespace Erdos199

/-- A set of reals is an infinite arithmetic progression. -/
def IsInfiniteAP (S : Set ℝ) : Prop :=
  ∃ a b : ℝ, b ≠ 0 ∧ S = {x | ∃ n : ℕ, x = a + n * b}

/--
If $A\subset \mathbb{R}$ does not contain a 3-term arithmetic progression then must $\mathbb{R}\backslash A$ contain an infinite arithmetic progression?

Baumgartner [Ba75] answered this in the negative.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos199.lean"]
theorem erdos_199 : answer(False) ↔
    ∀ A : Set ℝ, ThreeAPFree A →
      ∃ S : Set ℝ, IsInfiniteAP S ∧ S ⊆ Aᶜ := by
  sorry

end Erdos199
