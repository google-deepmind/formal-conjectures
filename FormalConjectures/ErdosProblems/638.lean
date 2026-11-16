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

public import FormalConjecturesUtil

/-!
# Erdős Problem 638

*References:*
- [erdosproblems.com/638](https://www.erdosproblems.com/638)
-/

@[expose] public section

namespace Erdos638

/--
A graph edge-coloring contains at least one monochromatic triangle.
-/
def HasMonochromaticTriangle {V : Type*} (G : SimpleGraph V)
  {C : Type*} (coloring : G.EdgeLabeling C) : Prop :=
  ∃ s : Finset V, G.IsNClique 3 s ∧
    ∃ k : C, ∀ e ∈ s.sym2, ∃ h : e ∈ G.edgeSet,
      coloring ⟨e, h⟩ = k

/--
A family of graphs is closed under taking finite subgraphs.
This condition is not part of the original formulation,
however as pointed out on [erdosproblems.com/638],
it is a necessary addition to make the problem relevant.
-/
def ClosedUnderFiniteSubgraphs {V : Type*} (S : Set (SimpleGraph V)) : Prop :=
  ∀ (G H : SimpleGraph V), G ∈ S → H ≤ G →
    H.support.Finite → H ∈ S

/--
A family of graphs is finite.
-/
def IsFiniteGraphFamily {V : Type*} (S : Set (SimpleGraph V)) : Prop :=
  ∀ G : SimpleGraph V, G ∈ S → G.support.Finite


/--
Original wording:
Let $S$ be a family of finite graphs, such that for every $n$ there is some $G_n ∈ S$,
such that if the edges of $G_n$ are colored with $n$ colors, then there is a monochromatic triangle.

Is it true, that for every infinite cardinal $ℵ$, there is a graph $G$
of which every finite subgraph is in $S$ and if the edges of $G$ are colored with $ℵ$ many colors,
then there is a monochromatic triangle.

Note: The intended question likely requires that $S$ be closed under taking finite subgraphs,
as a counterexample is otherwise reasonably easy to construct.
-/
@[category research open, question, AMS 5]
theorem erdos_638 {V : Type*} (S : Set (SimpleGraph V)) :
  ClosedUnderFiniteSubgraphs S ∧
  IsFiniteGraphFamily S ∧
  (∀ n : ℕ, ∃ G ∈ S,
    ∀ coloring : G.EdgeLabeling (Fin n),
      HasMonochromaticTriangle G coloring) →
  (∀ k : Cardinal, Cardinal.aleph0 ≤ k →
    ∃ G : SimpleGraph V,
      (∀ H : SimpleGraph V, H ≤ G → H.support.Finite → H ∈ S) ∧
      (∀ coloring : G.EdgeLabeling (Quotient.out k),
        HasMonochromaticTriangle G coloring)) := by
  sorry

end Erdos638
