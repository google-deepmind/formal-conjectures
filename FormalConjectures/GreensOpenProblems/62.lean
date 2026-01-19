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

open Filter

/-!
# Ben Green's Open Problem 62

Let $p$ be a large prime, and let $A$ be the set of all primes less than $p$.
Is every $x \in \{1, \ldots, p-1\}$ congruent to some product $a_1 a_2$ where $a_1, a_2 \in A$?

This is a problem of Erdős, Odlyzko, and Sárközy [105] from 1987.

*Reference:* [Ben Green's Open Problem 62](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.62)
-/

namespace Green62

/--
Let $p$ be a large prime, and let $A$ be the set of all primes less than $p$.
Is every $x \in \{1, \ldots, p-1\}$ congruent to some product $a_1 a_2$ where $a_1, a_2 \in A$?
-/
@[category research open, AMS 11]
theorem green_62 :
    answer(sorry) ↔
      ∀ᶠ p in atTop, p.Prime →
        let A := (Finset.range p).filter Nat.Prime
        ∀ x : ℕ, 1 ≤ x ∧ x < p →
          ∃ a₁ ∈ A, ∃ a₂ ∈ A, (x : ZMod p) = (a₁ * a₂ : ZMod p) := by
  sorry

end Green62
