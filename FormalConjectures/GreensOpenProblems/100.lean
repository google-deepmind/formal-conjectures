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
# Green's Open Problem 100

*Reference:* [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.100)

Is every group well-approximated by finite groups?

This problem asks whether every group is residually finite. A group is residually finite if
for every non-identity element, there exists a normal subgroup such that the quotient is finite
and the element is not contained in the normal subgroup.
-/

namespace Green100

/--
Is every group well-approximated by finite groups?

Equivalently, is every group residually finite? A group $G$ is residually finite if for every
non-identity element $g \in G$, there exists a normal subgroup $N$ such that $G/N$ is finite
and $g \notin N$.
-/
@[category research open, AMS 20]
theorem green_100 :
  answer(sorry) ↔
    ∀ (G : Type*) [Group G],
      (∀ (g : G), g ≠ 1 → ∃ (N : Subgroup G), N.Normal ∧ Finite (G ⧸ N) ∧ g ∉ N) := by
  sorry
end Green100
