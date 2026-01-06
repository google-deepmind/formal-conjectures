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
import Mathlib.SetTheory.Cardinal.Ordinal

/-!
# Erdős Problem 1068

*Reference:* [erdosproblems.com/1068](https://www.erdosproblems.com/1068)
-/

open Cardinal

namespace Erdos1068

/--
Two walks are internally disjoint if they share no vertices other than their endpoints.
-/
def InternallyDisjoint {V : Type*} {G : SimpleGraph V} {u v : V} (p q : G.Walk u v) : Prop :=
  Disjoint ({x | x ∈ p.support} \ {u, v}) ({x | x ∈ q.support} \ {u, v})

/--
We say a graph is infinitely connected if any two vertices are connected by infinitely many
pairwise disjoint paths.
-/
def InfinitelyConnected {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → ∃ P : Set (G.Walk u v),
    P.Infinite ∧ (∀ p ∈ P, p.IsPath) ∧ P.Pairwise InternallyDisjoint

/--
Does every graph with chromatic number $\aleph_1$ contain a countable subgraph which is
infinitely connected?
-/
@[category research open, AMS 5]
theorem erdos_1068 :
  (∀ (V : Type*) (G : SimpleGraph V), G.chromaticNumber = aleph 1 →
    ∃ (s : Set V), s.Countable ∧ InfinitelyConnected (G.induce s)) ↔ answer(sorry) := by
  sorry

end Erdos1068
