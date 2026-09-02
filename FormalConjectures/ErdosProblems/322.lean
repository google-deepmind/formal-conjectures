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

*References:*
- [erdosproblems.com/322](https://www.erdosproblems.com/322)
- [Er36] Erdős, Paul, *On the Representation of an Integer as the Sum of k k-th Powers*. J. London
  Math. Soc. (1936), 133-136.
- [Er65b] Erdős, Paul, *Some recent advances and current problems in number theory*. Lectures on
  Modern Mathematics, Vol. III (1965), 196-244.
- [Gu04] Guy, Richard K., *Unsolved problems in number theory*. (2004), xviii+437.
- [Ma36] Mahler, Kurt, *Note on Hypothesis K of Hardy and Littlewood*. J. London Math. Soc. (1936),
  136-138.
-/

namespace Erdos322

/-- For `k ≥ 3`, the number of ordered representations of `n` as a sum of `k` many `k`th
powers of positive integers. The bases can be restricted to the interval from `1` to `n`,
since `x ≤ x ^ k` for positive `x`. -/
def representationCount (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k → Fin (n + 1))).filter
    (fun a ↦ (∀ i, 0 < (a i : ℕ)) ∧ ∑ i, (a i : ℕ) ^ k = n)).card

/--
Let $k\geq 3$ and $A\subset \mathbb{N}$ be the set of $k$th powers. What is the order of growth of $1_A^{(k)}(n)$, i.e. the number of representations of $n$ as the sum of $k$ many $k$th powers? Does there exist some $c>0$ and infinitely many $n$ such that $$1_A^{(k)}(n) >n^c?$$
-/
@[category research open, AMS 11]
theorem erdos_322 : answer(sorry) ↔
    ∀ k : ℕ, 3 ≤ k → ∃ c > (0 : ℝ),
      {n : ℕ | (n : ℝ) ^ c < representationCount k n}.Infinite := by
  sorry

end Erdos322
