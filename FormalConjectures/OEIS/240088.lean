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
# Ways of writing $n$ as an ordered sum of a triangular, square, and pentagonal number

The sequence $a(n)$ counts the number of tuples $(i, j, k) \in \mathbb{N}^3$ such that
$T_i + S_j + P_k = n$, where $T_i = i(i+1)/2$, $S_j = j^2$, and $P_k = k(3k-1)/2$:
$$a(n) = |\{(i, j, k) \in \mathbb{N}^3 : i(i+1)/2 + j^2 + k(3k-1)/2 = n\}|$$

*References:*
- [A240088](https://oeis.org/A240088)
- [On universal sums of polygonal numbers](https://doi.org/10.1007/s11425-015-4994-4)
  by *Zhi-Wei Sun*, Sci. China Math. **58** (2015), 1367–1396.
-/

namespace OeisA240088

open Finset

/-- Number of ways of writing $n$ as an ordered sum of a triangular number, a square,
and a pentagonal number. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ range (n + 2), ∑ j ∈ range (n + 2), ∑ k ∈ range (n + 2),
    if i * (i + 1) / 2 + j ^ 2 + k * (3 * k - 1) / 2 = n then 1 else 0

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  decide

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by
  decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by
  decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by
  decide

/--
It is conjectured that $a(n)$ is always positive (Conjecture 1.1 of Sun (2009)).
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) : 0 < a n := by
  sorry

end OeisA240088
