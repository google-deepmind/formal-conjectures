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
# Erdős Problem 722

*References:*
- [erdosproblems.com/722](https://www.erdosproblems.com/722)
- [Ha61] Hanani, Haim, The existence and construction of balanced incomplete block designs. Ann.
  Math. Statist. (1961), 361-386.
- [Ke14] P. Keevash, The existence of designs. arXiv:1401.3665 (2014).
- [Wi72] Wilson, Richard M., An existence theory for pairwise balanced designs. {II}. The structure
  of {PBD}-closed sets and the existence conjectures. J. Combinatorial Theory Ser. A (1972), 246-273.
-/

namespace Erdos722

open Filter Asymptotics

/--
Let $k>r$ and $n$ be sufficiently large in terms of $k$ and $r$. Does there always exist a block
$r-(n,k,1)$ design (or Steiner system with parameters $(n,k,r)$), provided the trivial necessary
divisibility conditions $\binom{k-i}{r-i}\mid \binom{n-i}{r-i}$ are satisfied for every $0\leq i<r$?
That is, can one find a family of $\binom{n}{r}\binom{k}{r}^{-1}$ many subsets of $\{1,\ldots,n\}$,
all of size $k$, such that any $A\subseteq \{1,\ldots,n\}$ of size $r$ is contained in exactly one
set in the family?

This was proved by Keevash [Ke14] for all $(r,k)$.
-/
@[category research solved, AMS 5]
theorem erdos_722 :
    answer(True) ↔ ∀ r k : ℕ, 1 ≤ r → r < k → ∀ᶠ n : ℕ in atTop,
    (∀ i < r, (k - i).choose (r - i) ∣ (n - i).choose (r - i)) →
      ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign r k := by
  sorry

end Erdos722
