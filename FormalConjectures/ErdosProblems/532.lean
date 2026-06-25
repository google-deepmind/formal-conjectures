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
# Erdős Problem 532

*Reference:* [erdosproblems.com/532](https://www.erdosproblems.com/532)
-/

namespace Erdos532

/--
If the natural numbers are $2$-coloured, then there is an infinite set $A \subseteq \mathbb{N}$
whose nonempty finite subset sums are all the same colour. The answer is yes, a consequence of
Hindman's theorem.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos532.lean"]
theorem erdos_532 (c : ℕ → Fin 2) :
    ∃ A : Set ℕ, A.Infinite ∧
      ∃ color : Fin 2,
        ∀ S : Finset ℕ, S.Nonempty → ↑S ⊆ A →
          c (∑ n ∈ S, n) = color := by
  sorry

end Erdos532
