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
# Erdős Problem 1020

*Reference:* [erdosproblems.com/1020](https://www.erdosproblems.com/1020)
-/

namespace Erdos1020

/-- The maximum number of edges in an `r`-uniform hypergraph on `n` vertices containing no
matching of size `k` (i.e. no `k` pairwise vertex-disjoint edges). -/
noncomputable def f (n r k : ℕ) : ℕ :=
  open scoped Classical in
  let candidates :=
    (((Finset.univ : Finset (Fin n)).powersetCard r).powerset).filter fun H ↦
      ¬ ∃ M : Finset (Finset (Fin n)),
          M ⊆ H ∧ M.card = k ∧ (M : Set (Finset (Fin n))).PairwiseDisjoint id
  candidates.sup Finset.card

/--
Let $f(n;r,k)$ be the maximal number of edges in an $r$-uniform hypergraph which contains no set of $k$ many independent edges.

For all $r\geq 3$, $$f(n;r,k)=\max\left(\binom{rk-1}{r}, \binom{n}{r}-\binom{n-k+1}{r}\right).$$

Note: the source states the formula with no range on `n` or `k`, but some restriction
is needed: e.g. for `r = 3`, `k = 2`, `n = 4` no two disjoint triples fit in `4`
vertices, so the left-hand side is `4.choose 3 = 4` while the right-hand side is
`5.choose 3 = 10`. We require `k ≥ 1` and `n ≥ r*k - 1`: this is the smallest `n`
accommodating the construction counted by the first term (all `r`-subsets of a fixed
`(r*k - 1)`-set), and at `n = r*k - 1` the equality holds trivially, since the complete
`r`-uniform hypergraph has no `k`-matching. The source's commentary likewise calls the
case `n < k*r` trivial.
-/
@[category research open, AMS 5]
theorem erdos_1020 :
    ∀ (r : ℕ), 3 ≤ r → ∀ n k : ℕ, 0 < k → r * k - 1 ≤ n →
      f n r k = max ((r * k - 1).choose r) (n.choose r - (n - k + 1).choose r) := by
  sorry

end Erdos1020
