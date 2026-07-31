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
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.ChromaticNumber
import Mathlib.SetTheory.Cardinal.Ordinal

/-!
# Erdős Problem 62

*Reference:* [erdosproblems.com/62](https://www.erdosproblems.com/62)

If $G_1,G_2$ are two graphs with chromatic number $\aleph_1$ then must there exist
a graph $G$ whose chromatic number is $4$ (or even $\aleph_0$) which is a subgraph
of both $G_1$ and $G_2$?
-/

namespace Erdos62

open SimpleGraph Cardinal

/--
A graph `H` is a subgraph of `G` if there is an injective embedding of the vertices
that preserves adjacency.
-/
def isSubgraph {V W : Type*} (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∃ (f : V ↪ W), ∀ a b, H.adj a b → G.adj (f a) (f b)

/--
Conjecture: Any two graphs of chromatic number ℵ₁ have a common subgraph
of chromatic number 4.
-/
@[category research open, AMS 52]
theorem erdos_62_4 {V1 V2 : Type} (G1 : SimpleGraph V1) (G2 : SimpleGraph V2)
    (h1 : chromaticNumber G1 = aleph 1) (h2 : chromaticNumber G2 = aleph 1) :
    ∃ (H : Type) [SimpleGraph H],
      isSubgraph H G1 ∧ isSubgraph H G2 ∧ chromaticNumber H = 4 := by
  sorry

/--
Conjecture: Any two graphs of chromatic number ℵ₁ have a common subgraph
of chromatic number ℵ₀.
-/
@[category research open, AMS 52]
theorem erdos_62_aleph0 {V1 V2 : Type} (G1 : SimpleGraph V1) (G2 : SimpleGraph V2)
    (h1 : chromaticNumber G1 = aleph 1) (h2 : chromaticNumber G2 = aleph 1) :
    ∃ (H : Type) [SimpleGraph H],
      isSubgraph H G1 ∧ isSubgraph H G2 ∧ chromaticNumber H = aleph 0 := by
  sorry

end Erdos62
