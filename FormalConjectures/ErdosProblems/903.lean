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
# Erdős Problem 903

A conjecture of Erdős and Sós. For a prime power $p$ and $n = p^2 + p + 1$, if a pairwise
balanced design on $n$ points has more than $n$ blocks, then it must have at least $n + p$
blocks. Proved by Erdős, Fowler, Sós, and Wilson [EFSW85].

*Reference:* [erdosproblems.com/903](https://www.erdosproblems.com/903)

[Er82e] Erdős, P., _Problems and results in combinatorics and graph theory_, 1982.

[dBEr48] de Bruijn, N.G. and Erdős, P., _On a combinatorial problem_,
Nederl. Akad. Wetensch., Proc. **51** (1948), 1277–1279.

[EFSW85] Erdős, P., Fowler, J.C., Sós, V.T., and Wilson, R.M., _On 2-designs_,
J. Combin. Theory Ser. A (1985), 131–142.
-/

namespace Erdos903

/-- A pairwise balanced design on $\operatorname{Fin}(n)$: a family of blocks (subsets), each of
size at least 2, such that every pair of distinct elements is contained in exactly one
block. -/
def IsPairwiseBalancedDesign {n : ℕ} (blocks : Finset (Finset (Fin n))) : Prop :=
  (∀ B ∈ blocks, 2 ≤ B.card) ∧
  (∀ x y : Fin n, x ≠ y →
    ∃! B : Finset (Fin n), B ∈ blocks ∧ x ∈ B ∧ y ∈ B)

/--
Erdős Problem 903, a conjecture of Erdős and Sós [Er82e]:

Let $n = p^2 + p + 1$ for a prime power $p$ (i.e., $p = q^k$ for some prime $q$ and
$k \geq 1$), and let blocks be a pairwise balanced design on $\{0, \ldots, n-1\}$ (every
pair of distinct elements appears in exactly one block, and every block has at least 2
elements). If the number of blocks $t > n$, then $t \geq n + p$.

Proved by Erdős, Fowler, Sós, and Wilson [EFSW85].
-/
@[category research solved, AMS 5]
theorem erdos_903 (p q k : ℕ) (hq : Nat.Prime q) (hk : k ≥ 1)
    (hp : p = q ^ k)
    (n : ℕ) (hn : n = p ^ 2 + p + 1)
    (blocks : Finset (Finset (Fin n)))
    (hdesign : IsPairwiseBalancedDesign blocks)
    (hgt : blocks.card > n) :
    blocks.card ≥ n + p := by
  sorry

end Erdos903
