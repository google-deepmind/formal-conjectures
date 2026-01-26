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
# Ben Green's Open Problem 82

Let $A \subset \mathbb{Z}$ be a set of size $n$. For how many $\theta \in \mathbb{R}/\mathbb{Z}$
must we have $\sum_{a \in A} \cos(2\pi a\theta) = 0$?

This problem asks for the minimum number of zeros of the trigonometric sum
$\sum_{a \in A} \cos(2\pi a \theta)$ on the circle, over all sets $A$ of a given size.

*Reference:*
- [Gr24] [Ben Green's Open Problem 82](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.82)
-/

open Real Set
open scoped Finset

namespace Green82

/--
Let $A \subset \mathbb{Z}$ be a set of size $n$. For how many $\theta \in \mathbb{R}/\mathbb{Z}$
must we have $\sum_{a \in A} \cos(2\pi a\theta) = 0$?

We formalize this as asking for the infimum of the number of zeros of
$\theta \mapsto \sum_{a \in A} \cos(2\pi a \theta)$ in $[0, 1)$, over all finite sets
$A \subset \mathbb{Z}$ with $|A| = n$.
-/
@[category research open, AMS 11 42]
theorem green_82 (n : ℕ) (hn : 1 ≤ n) :
    ⨅ (A : Finset ℤ) (_ : A.card = n),
      ({θ : ℝ | θ ∈ Ico 0 1 ∧ ∑ a ∈ A, cos (2 * π * a * θ) = 0} : Set ℝ).ncard =
    answer(sorry) := by
  sorry

end Green82
