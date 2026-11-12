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
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

/-!
# Edge colourings of a SimpleGraph

`SimpleGraph.IsEdgeColouring H c` asserts that `c : ι → SimpleGraph V` is a partition of
the edges of `H` into colour classes indexed by `ι`. The classes must (1) cover `H`
(`H = ⨆ i, c i`) and (2) be pairwise disjoint (each edge belongs to exactly one class).

This unifies the previous local `IsNEdgeColouring` (`ι = Fin n`) and `IsCountableEdgeColouring`
(`ι = ℕ`) shapes used in `FormalConjectures/ErdosProblems/596.lean`. The two are now special
cases of `IsEdgeColouring` parameterised by the index type.

`SimpleGraph.IsProperEdgeColouring c` asserts that the edge colouring `c` is proper, i.e.
no two adjacent edges are assigned the same colour.

`SimpleGraph.IsAcyclicEdgeColouring c` asserts that the edge colouring `c` is acyclic, i.e. proper
and with no 2-coloured cycle.

`SimpleGraph.AcyclicEdgeColourable G k` asserts that the graph `G` has an acyclic edge colouring
with at most `k` colours.

`SimpleGraph.TopEdgeLabeling.CliqueFree` is the Ramsey-theoretic condition on the other
edge-colouring shape Mathlib provides, a labelling of the edges of the complete graph: no
colour class contains a clique of the given size.
-/

namespace SimpleGraph

/-- `IsEdgeColouring H c` asserts that `c : ι → SimpleGraph V` is a partition of the edges
of `H`: the colour classes cover `H` (`H = ⨆ i, c i`) and are pairwise disjoint. -/
def IsEdgeColouring {V ι : Type*} (H : SimpleGraph V) (c : ι → SimpleGraph V) : Prop :=
  H = ⨆ i, c i ∧ ∀ i j, i ≠ j → Disjoint (c i) (c j)

/-- An edge colouring `c : ι → SimpleGraph V` is proper if no two adjacent edges are assigned
the same colour, i.e. there is no path of length 2 in a colour class. -/
def IsProperEdgeColouring {V ι : Type*} (c : ι → SimpleGraph V) : Prop :=
  ∀ (i : ι) (v u w : V), (c i).Adj v u → (c i).Adj v w → u = w

/-- An acyclic edge colouring is a proper edge colouring `c : ι → SimpleGraph V` with no
2-coloured cycle, i.e. the union of any two colour classes is acyclic. -/
def IsAcyclicEdgeColouring {V ι : Type*} (c : ι → SimpleGraph V) : Prop :=
  IsProperEdgeColouring c ∧ ∀ a b : ι, (c a ⊔ c b).IsAcyclic

/-- `AcyclicEdgeColourable G k` asserts that the graph `G` has an acyclic edge colouring
with at most `k` colours. -/
def AcyclicEdgeColourable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : Fin k → SimpleGraph V, IsEdgeColouring G c ∧ IsAcyclicEdgeColouring c

/-- A labelling of the edges of the complete graph on `V` by `ι` is `n`-clique-free when no
colour class contains an `n`-clique, that is, when it admits no monochromatic `n`-clique. -/
def TopEdgeLabeling.CliqueFree {V ι : Type*} (C : TopEdgeLabeling V ι) (n : ℕ) : Prop :=
  ∀ i : ι, (C.labelGraph i).CliqueFree n

end SimpleGraph
