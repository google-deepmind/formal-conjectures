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
# Erdős Problem 903

*References:*
- [erdosproblems.com/903](https://www.erdosproblems.com/903)
- [EFSW85] Erdős, P. and Fowler, Joel C. and S\'os, Vera T. and Wilson, Richard M., On {$2$}-designs.
J. Combin. Theory Ser. A (1985), 131--142.
- [dBEr48] de Bruijn, N. G. and Erdős, P., On a combinatorial problem. Nederl. Akad. Wetensch.,
Proc. (1948), 1277--1279 = Indagationes Math. 10, 421--423.
-/

namespace Erdos903

open Filter Asymptotics

/--
Let $n=p^2+p+1$ for some prime power $p$, and let $A_1,\ldots,A_t\subseteq \{1,\ldots,n\}$ be a
block design (so that every pair $x,y\in \{1,\ldots,n\}$ is contained in exactly one $A_i$). Is it
true that if $t>n$ then $t\geq n+p$?

This is true, and was proved by Erdős, Fowler, Sós, and Wilson [EFSW85].
-/
@[category research solved, AMS 5]
theorem erdos_903 :
    answer(True) ↔ ∀ p : ℕ, IsPrimePow p →
    ∀ H : Finset (Finset (Fin (p ^ 2 + p + 1))),
      H.IsPairwiseBalancedDesign → p ^ 2 + p + 1 < H.card →
        p ^ 2 + p + 1 + p ≤ H.card := by
  sorry

end Erdos903
