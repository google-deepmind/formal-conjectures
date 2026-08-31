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

/-!
# Erdős Problem 773

*References:*
- [erdosproblems.com/773](https://www.erdosproblems.com/773)
- [AlEr85] Alon, Noga and Erdős, P., *An application of graph theory to additive number theory*.
  European J. Combin. (1985), 201-203.
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [LeTh95] Lefmann, Hanno and Thiele, Torsten, *Point sets with distinct distances*. Combinatorica
  (1995), 379--408.
-/

namespace Erdos773

open Filter

/--
What is the size of the largest Sidon subset $A\subseteq\{1,2^2,\ldots,N^2\}$? Is it $N^{1-o(1)}$?
-/
@[category research open, AMS 11]
theorem erdos_773 : answer(sorry) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 - ε) ≤
        (Finset.maxSidonSubsetCard
          (Finset.image (fun n : ℕ => n ^ 2) (Finset.Icc 1 N)) : ℝ) := by
  sorry

end Erdos773
