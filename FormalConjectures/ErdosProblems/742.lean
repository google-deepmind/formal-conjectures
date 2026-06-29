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
# Erdős Problem 742

The Murty-Simon Conjecture: every diameter-2-critical graph on $n$ vertices has
at most $\lfloor n^2/4 \rfloor$ edges.

*References:*
* [erdosproblems.com/742](https://www.erdosproblems.com/742)
* Murty, U.S.R. and Simon, J.
-/

namespace Erdos742

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A simple graph has diameter at most 2 if every two distinct vertices are connected
by a path of length at most 2. -/
def hasDiameterAtMostTwo (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → G.Adj u v ∨ ∃ w : V, G.Adj u w ∧ G.Adj w v

/-- A simple graph is *diameter-2-critical* if it has diameter at most 2, and for every
edge, removing that edge results in the graph no longer having diameter at most 2. -/
def isDiameterTwoCritical (G : SimpleGraph V) : Prop :=
  hasDiameterAtMostTwo G ∧
    ∀ e ∈ G.edgeSet, ¬hasDiameterAtMostTwo (G.deleteEdges {e})

/-- **Murty-Simon Conjecture** (Erdős Problem 742): Every diameter-2-critical graph on
$n$ vertices has at most $\lfloor n^2/4 \rfloor$ edges. -/
@[category research open, AMS 5]
theorem erdos_742 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : isDiameterTwoCritical G) :
    G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4 := by
  sorry

end Erdos742
