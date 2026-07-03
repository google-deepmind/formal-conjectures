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
# Erdős Problem 328

*References:*
- [erdosproblems.com/328](https://www.erdosproblems.com/328)
- [Er80e] Erdős, P., *Some applications of Ramsey's theorem to additive number theory*.
  European J. Combin. (1980), 43-46.
- [NeRo85] J. Nešetřil and V. Rödl, *Two proofs in combinatorial number theory*.
  Proc. Amer. Math. Soc. (1985), 185-188.
-/

open AdditiveCombinatorics

namespace Erdos328

/--
Suppose $A\subseteq\mathbb{N}$ and $C>0$ is such that $1_A\ast 1_A(n)\leq C$ for all
$n\in\mathbb{N}$. Can $A$ be partitioned into $t$ many subsets $A_1,\ldots,A_t$ (where
$t=t(C)$ depends only on $C$) such that $1_{A_i}\ast 1_{A_i}(n)<C$ for all $1\leq i\leq t$
and $n\in \mathbb{N}$?

The answer is no. Asked by Erdős and Newman. Nešetřil and Rödl [NeRo85] have shown the
answer is no for all $C$ (even if $t$ is also allowed to depend on $A$).

Erdős [Er80e] had previously shown the answer is no for $C=3,4$ and infinitely many other
values of $C$.

See also [774].
-/
@[category research solved, AMS 11]
theorem erdos_328 : answer(False) ↔
    ∀ C : ℕ, 0 < C →
      ∃ t : ℕ, ∀ A : Set ℕ, (∀ n, sumRep A n ≤ C) →
        ∃ P : Fin t → Set ℕ, (⋃ i, P i) = A ∧
          Set.univ.PairwiseDisjoint P ∧
          ∀ i, ∀ n, sumRep (P i) n < C := by
  sorry

end Erdos328
