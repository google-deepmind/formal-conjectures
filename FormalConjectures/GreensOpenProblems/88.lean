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

import FormalConjecturesUtil
import FormalConjectures.Arxiv.«1609.08688».sIncreasingrTuples

/-!
# Ben Green's Open Problem 88

*References:*
- [Gr24] [Ben Green's Open Problem
  88](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.88)
- [GoLo21] [The length of an $s$-increasing sequence of
  $r$-tuples](https://arxiv.org/abs/1609.08688)
  by W. T. Gowers and J. Long
-/

open Arxiv.«1609.08688»

namespace Green88

/--
[Gr24, Problem 88]: Is there an absolute constant $\delta > 0$ such that every pairwise
$2$-comparable set $S \subseteq [N]^3$ satisfies $|S| \leq N^{2 - \delta}$?
-/
@[category research open, AMS 5 52]
theorem green_88 :
    answer(sorry) ↔
      ∃ δ > (0 : ℝ), ∀ (N : ℕ) (S : Finset (Fin 3 → Fin N)),
        (S : Set (Fin 3 → Fin N)).Pairwise IsComparable₂ →
          (S.card : ℝ) ≤ (N : ℝ) ^ (2 - δ) := by
  sorry

end Green88
