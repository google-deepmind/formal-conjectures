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
# Green's Open Problem 52

*Reference:* [Green's Open Problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.52)

-/

open Filter Real
open scoped Pointwise

namespace Green52

/--
Suppose that $A \subset \mathbb{F}_2^n$ is a set with an additive complement of size $K$.
Does $2A$ contain a coset of codimension $O_K(1)$?
-/
@[category research open, AMS 5 11]
theorem green_52 :
    answer(sorry) ↔ ∃ (c : ℕ → ℕ), ∀ (n K : ℕ) (A : Set (𝔽₂ n)) (S : Finset (𝔽₂ n)),
      S.card = K → A + (S : Set (𝔽₂ n)) = Set.univ →
      ∃ (V : AffineSubspace (ZMod 2) (𝔽₂ n)), (V : Set (𝔽₂ n)) ⊆ A + A ∧
        n ≤ Module.finrank (ZMod 2) V.direction + c K := by
  sorry

/--
Could $2A$ even contain a coset of codimension $O(\log K)$?
-/
@[category research open, AMS 5 11]
theorem green_52_log :
    answer(sorry) ↔ ∃ (C D : ℝ), ∀ (n K : ℕ) (A : Set (𝔽₂ n)) (S : Finset (𝔽₂ n)),
      0 < K → S.card = K → A + (S : Set (𝔽₂ n)) = Set.univ →
      ∃ (V : AffineSubspace (ZMod 2) (𝔽₂ n)), (V : Set (𝔽₂ n)) ⊆ A + A ∧
        (n : ℝ) ≤ (Module.finrank (ZMod 2) V.direction : ℝ) + C * log (K : ℝ) + D := by
  sorry

-- TODO(jgd): Implement variants from Green's comments [Gr24].

end Green52
