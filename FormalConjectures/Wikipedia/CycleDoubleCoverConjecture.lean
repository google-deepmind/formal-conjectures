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
# The cycle double cover conjecture (Szekeres 1973, Seymour 1979)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Cycle_double_cover)
* [Sz73] Szekeres, G. (1973). "Polyhedral decompositions of cubic graphs."
  *Bull. Austral. Math. Soc.* 8, pp. 367--387.
* [Se79] Seymour, P. D. (1979). "Sums of circuits." In *Graph Theory and Related Topics*,
  Academic Press, pp. 341--355.
* [Ja85] Jaeger, F. (1985). "A survey of the cycle double cover conjecture." In *Cycles in
  Graphs*, North-Holland Math. Stud. 115, pp. 1--12.
* [Go85] Goddyn, L. (1985). "A girth requirement for the double cycle cover conjecture." In
  *Cycles in Graphs*, North-Holland Math. Stud. 115, pp. 13--26.
* [Zh97] Zhang, C.-Q. (1997). *Integer flows and cycle covers of graphs.* Marcel Dekker.
-/

open SimpleGraph

namespace CycleDoubleCoverConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- A multiset of cycles `C` is a **cycle double cover** of `G` if every edge of `G` lies on
exactly two of the cycles (counted with multiplicity in `C`). -/
def IsCycleDoubleCover (G : SimpleGraph V) [DecidableRel G.Adj] (C : Multiset (Cycle G)) : Prop :=
  ∀ e ∈ G.edgeFinset, (C.filter fun c => e ∈ c.edges).card = 2

/--
**The cycle double cover conjecture (Szekeres 1973, Seymour 1979).**

Every finite bridgeless graph has a family of cycles such that every edge lies on exactly two
of them.
-/
@[category research open, AMS 5]
theorem cycle_double_cover_conjecture :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsBridgeless → ∃ C : Multiset (Cycle G), IsCycleDoubleCover G C := by
  sorry

/--
**Reduction to cubic graphs (Jaeger 1985).**

The conjecture is equivalent to its restriction to bridgeless cubic graphs: if every bridgeless
cubic graph has a cycle double cover, then every bridgeless graph does.

*Reference:* [Ja85].
-/
@[category research solved, AMS 5]
theorem cycle_double_cover_conjecture.variants.cubic_reduction :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ v, G.degree v = 3) → G.IsBridgeless →
        ∃ C : Multiset (Cycle G), IsCycleDoubleCover G C) →
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsBridgeless → ∃ C : Multiset (Cycle G), IsCycleDoubleCover G C := by
  sorry

/--
**A minimal counterexample would be a snark of girth at least 12 (Goddyn 1985; Huck 2000).**

Every bridgeless cubic graph of girth at most $11$ has a cycle double cover.

*Reference:* [Go85].
-/
@[category research solved, AMS 5]
theorem cycle_double_cover_conjecture.variants.girth_le_eleven
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless) (hgirth : G.girth ≤ 11) :
    ∃ C : Multiset (Cycle G), IsCycleDoubleCover G C := by
  sorry

/--
**Edgeless graphs.**

A graph with no edges is bridgeless and has the empty cycle double cover.
-/
@[category test, AMS 5]
theorem cycle_double_cover_conjecture.variants.edgeless
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.edgeFinset = ∅) : ∃ C : Multiset (Cycle G), IsCycleDoubleCover G C :=
  ⟨0, fun e he => by simp [h] at he⟩

end CycleDoubleCoverConjecture
