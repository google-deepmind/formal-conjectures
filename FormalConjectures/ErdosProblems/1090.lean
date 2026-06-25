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
# Erdős Problem 1090

*Reference:* [erdosproblems.com/1090](https://www.erdosproblems.com/1090)
-/

namespace Erdos1090

/--
For every $k \ge 3$ there is a finite set $A \subseteq \mathbb{R}^2$ such that in every
2-colouring of $A$ there is a line $S$ containing at least $k$ points of $A$, such that
every point of $A$ on that line lies in $S$ and all of them have the same colour.
The answer is yes (Hunter), via the Hales–Jewett theorem.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1090.lean"]
theorem erdos_1090 (k : ℕ) (hk : 3 ≤ k) :
    ∃ (A : Finset (Fin 2 → ℝ)), ∀ (C : A → Fin 2),
      ∃ (S : Finset (Fin 2 → ℝ)), ∃ (hSA : S ⊆ A),
        Collinear ℝ (S : Set (Fin 2 → ℝ)) ∧ S.card ≥ k ∧
          (∀ y ∈ A, y ∈ affineSpan ℝ (S : Set (Fin 2 → ℝ)) → y ∈ S) ∧
          ∃ c, ∀ x (hx : x ∈ S), C ⟨x, hSA hx⟩ = c := by
  sorry

end Erdos1090
