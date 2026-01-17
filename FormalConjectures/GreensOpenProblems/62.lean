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
# Ben Green's Open Problem 62

*Reference:* [Ben Green's Open Problem 62](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.8 Problem 62)
-/

open Filter

namespace Green62

/--
Let $p$ be a large prime, and let $A$ be the set of all primes less than $p$.
Is every $x ∈ \{1, \ldots, p - 1\}$ congruent to some product $a_1 a_2$ where $a_1, a_2 ∈ A$?

This is a problem of Erdős, Odlyzko, and Sárközy from 1987. Walker showed the result holds
for 6-fold products, and Shparlinski improved this to 5. Matomäki and Teräväinen (2023)
made significant progress, reducing the number of factors to 3.
-/
@[category research open, AMS 11]
theorem green_62 :
    answer(sorry) ↔ ∀ᶠ p in atTop, p.Prime →
      ∀ x ∈ Finset.Icc 1 (p - 1),
        ∃ a₁ a₂ : ℕ, a₁.Prime ∧ a₂.Prime ∧ a₁ < p ∧ a₂ < p ∧ x ≡ a₁ * a₂ [MOD p] := by
  sorry

end Green62

