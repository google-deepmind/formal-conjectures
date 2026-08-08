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
# Green's Open Problem 53

*References:*
- [Gr24] [Green's Open Problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.53)

-/

open Filter Function Real
open scoped Pointwise

namespace Green53

/--
Suppose that $\mathbb{F}_2^n$ is partitioned in to sets $A_1, ..., A_K$.
Does $2A_i$ contain a coset of codimension $O_K(1)$ for some $i$?
-/
@[category research open, AMS 5 11]
theorem green_53 :
    answer(sorry) ↔ ∃ (c : ℕ → ℕ), ∀ (n K : ℕ) (A : Fin K → Set (𝔽₂ n)),
      (⋃ i, A i) = Set.univ →
      Pairwise (Disjoint on A) →
      ∃ (i : Fin K) (S : AffineSubspace (ZMod 2) (𝔽₂ n)),
        (S : Set (𝔽₂ n)) ⊆ A i + A i ∧
        n ≤ Module.finrank (ZMod 2) S.direction + c K := by
  sorry

-- TODO(jgd): Implement variants from Green's comments [Gr24].

end Green53
