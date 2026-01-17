/-
Copyright 2025 The Formal Conjectures Authors.

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
# Green's Open Problem 23

Suppose that $\mathbb{N}$ is finitely coloured. Are there $x,y$ of the same colour such that $x^2 +
 y^2$ is a square?

References:
- [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.23)
- [FrKlMo25] Frantzikinakis, N., O. Klurman, and J. Moreira. "Partition regularity of Pythagorean pairs." Forum of Mathematics, Pi 13. Cambridge University Press (2025).
-/

namespace Green23

/--
Suppose that $\mathbb{N}$ is finitely coloured. Are there $x,y$ of the same colour such that $x^2 +
 y^2$ is a square?

Solved in [FrKlMo25].
-/
@[category research solved, AMS 5 11]
theorem green_23 :
  answer(True) ↔
    -- For every finite colouring of the natural numbers
    ∀ (k : ℕ) (c : ℕ → Fin k),
    -- there exist two numbers of the same colour whose squares sum to a square
    ∃ x y : ℕ, c x = c y ∧ IsSquare (x^2 + y^2) := by
  sorry

end Green23
