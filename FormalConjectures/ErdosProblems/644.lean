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
# Erdős Problem 644

*References:*
- [erdosproblems.com/644](https://www.erdosproblems.com/644)
- [EFKT92] Erdős, P. and Fon-Der-Flaass, D. and Kostochka, A. V. and Tuza, Zs., Small transversals in
uniform hypergraphs. Siberian Adv. Math. (1992), 82-88.
-/

namespace Erdos644

open Filter Asymptotics

/--
Let $f(k,r)$ be minimal such that if $A_1,A_2,\ldots$ is a family of sets, all of size $k$, such
that for every collection of $r$ of the $A_is$ there is some pair $\{x,y\}$ which intersects all of
the $A_j$, then there is some set of size $f(k,r)$ which intersects all of the sets $A_i$. Is it
true that
$$f(k,7)=(1+o(1))\frac{3}{4}k?$$
Is it true that for any $r\geq 3$ there exists some constant $c_r$ such that
$$f(k,r)=(1+o(1))c_rk?$$
-/
@[category research open, AMS 5]
theorem erdos_644.parts.i :
    answer(sorry) ↔
    (fun k ↦ ((Hypergraph.subfamilyTransversalBound k 7 2).toNat : ℝ)) ~[atTop]
      (fun k ↦ (3 / 4 : ℝ) * k) := by
  sorry

/--
For every $r\geq 3$, is there $c_r>0$ such that $f(k,r)=(1+o(1))c_rk$?
-/
@[category research open, AMS 5]
theorem erdos_644.parts.ii :
    answer(sorry) ↔ ∀ r : ℕ, 3 ≤ r → ∃ c : ℝ, 0 < c ∧
    (fun k ↦ ((Hypergraph.subfamilyTransversalBound k r 2).toNat : ℝ)) ~[atTop]
      (fun k ↦ c * k) := by
  sorry

end Erdos644
