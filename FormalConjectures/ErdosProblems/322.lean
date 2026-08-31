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
# Erdős Problem 322

*Reference:* [erdosproblems.com/322](https://www.erdosproblems.com/322)
-/

namespace Erdos322

/-- For `k ≥ 3`, the number of ordered representations of `n` as a sum of `k` many `k`th
powers of nonnegative integers. The bases can be restricted to the interval from `0` to `n`. -/
def representationCount (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k → Fin (n + 1))).filter
    (fun a ↦ ∑ i, (a i : ℕ) ^ k = n)).card

/--
Let $k\geq 3$ and $A\subset \mathbb{N}$ be the set of $k$th powers. What is the order of growth of $1_A^{(k)}(n)$, i.e. the number of representations of $n$ as the sum of $k$ many $k$th powers? Does there exist some $c>0$ and infinitely many $n$ such that $$1_A^{(k)}(n) >n^c?$$
-/
@[category research open, AMS 11]
theorem erdos_322 : answer(sorry) ↔
    ∀ k : ℕ, 3 ≤ k → ∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ) ^ c < representationCount k n}.Infinite := by
  sorry

end Erdos322
