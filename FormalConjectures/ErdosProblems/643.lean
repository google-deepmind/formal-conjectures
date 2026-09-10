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
# Erdős Problem 643

*References:*
- [erdosproblems.com/643](https://www.erdosproblems.com/643)
- [Fu84] F\"uredi, Z., Hypergraphs in which all disjoint pairs have distinct unions. Combinatorica
  (1984), 161--168.
- [PiVe09] Pikhurko, Oleg and Verstra\"{e}te, Jacques, The maximum size of hypergraphs without
  generalized 4-cycles. J. Combin. Theory Ser. A (2009), 637--649.
-/

namespace Erdos643

open Filter Asymptotics

/--
Let $f(n;t)$ be minimal such that if a $t$-uniform hypergraph on $n$ vertices contains at least
$f(n;t)$ edges then there must be four edges $A,B,C,D$ such that
$$A\cup B= C\cup D$$
and
$$A\cap B=C\cap D=\emptyset.$$
Estimate $f(n;t)$ - in particular, is it true that for $t\geq 3$
$$f(n;t)=(1+o(1))\binom{n}{t-1}?$$
-/
@[category research open, AMS 5]
theorem erdos_643.parts.i :
    let f : ℕ → ℕ → ℝ := answer(sorry)
    ∀ t : ℕ, 1 ≤ t →
      (fun n ↦ ((Hypergraph.extremalNumber n t
        (fun H ↦ ¬ H.HasRepeatedDisjointUnion) + 1 : ℕ) : ℝ)) ~[atTop] f t := by
  sorry

/--
Is it true that $f(n;t)=(1+o(1))\binom{n}{t-1}$ for $t\geq 3$?
-/
@[category research open, AMS 5]
theorem erdos_643.parts.ii :
    answer(sorry) ↔ ∀ t : ℕ, 3 ≤ t →
    (fun n ↦ ((Hypergraph.extremalNumber n t
      (fun H ↦ ¬ H.HasRepeatedDisjointUnion) + 1 : ℕ) : ℝ)) ~[atTop]
        (fun n ↦ (n.choose (t - 1) : ℝ)) := by
  sorry

end Erdos643
