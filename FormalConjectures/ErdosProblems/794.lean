/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 794

*References:* [erdosproblems.com/794](https://www.erdosproblems.com/794)

Is it true that every 3-uniform hypergraph on 3n vertices with at least n³+1 edges
must contain either:
  (a) a subgraph on 4 vertices with 3 edges, or
  (b) a subgraph on 5 vertices with 7 edges?

## Answer: NO

Disproved by Phillip Harris with an explicit counterexample: a 3-uniform hypergraph
on 9 vertices with 28 edges that avoids both forbidden configurations.

### Counterexample Construction (Harris)
- Vertices: {0,...,8} partitioned into A={0,1,2}, B={3,4,5}, C={6,7,8}
- Edges: All 27 transversal edges (one vertex from each part) plus {0,1,2}
- Total: 28 = 3³+1 edges on 9 = 3·3 vertices

The transversal structure ensures no 4 vertices can span 3+ edges because:
- Any 4 vertices must have ≥2 in some part (pigeonhole)
- Transversal edges have exactly 1 vertex from each part
- So at most 2 transversal edges fit in any 4-vertex set
- The edge {0,1,2} is fully in part A, so any 4-set containing it has ≥3 vertices
  from A, leaving ≤1 vertex from B∪C, which cannot support any transversal edge.

Balogh observed that condition (b) is actually redundant: any 5-vertex 3-graph
with 7 edges necessarily contains a 4-vertex subgraph with 3 edges.
-/

namespace Erdos794

/-- Harris's counterexample: 28 edges on 9 vertices forming a 3-uniform hypergraph
that contains no 4-vertex subgraph with 3+ edges. -/
def HarrisCounterexample : Finset (Finset (Fin 9)) := {
  -- The 27 transversal edges {a,b,c} with a ∈ {0,1,2}, b ∈ {3,4,5}, c ∈ {6,7,8}
  {0,3,6}, {0,3,7}, {0,3,8}, {0,4,6}, {0,4,7}, {0,4,8}, {0,5,6}, {0,5,7}, {0,5,8},
  {1,3,6}, {1,3,7}, {1,3,8}, {1,4,6}, {1,4,7}, {1,4,8}, {1,5,6}, {1,5,7}, {1,5,8},
  {2,3,6}, {2,3,7}, {2,3,8}, {2,4,6}, {2,4,7}, {2,4,8}, {2,5,6}, {2,5,7}, {2,5,8},
  -- The extra edge {0,1,2}
  {0,1,2}
}

/-- A finite hypergraph is *3-uniform* if every edge has exactly 3 vertices. -/
def Is3Uniform {α : Type*} (H : Finset (Finset α)) : Prop :=
  ∀ e ∈ H, e.card = 3

/-- `HasAtLeastEdgesOnVertices H k m` means there exists a set `S` of `k` vertices
which spans at least `m` edges of `H`. -/
def HasAtLeastEdgesOnVertices {α : Type*} [Fintype α] [DecidableEq α]
    (H : Finset (Finset α)) (k m : ℕ) : Prop :=
  ∃ (S : Finset α) (_ : S ∈ Finset.univ.powersetCard k),
    (H.filter (fun e => e ⊆ S)).card ≥ m

/-- A subgraph on 4 vertices with (at least) 3 edges. -/
abbrev Has4Vertices3Edges {α : Type*} [Fintype α] [DecidableEq α] (H : Finset (Finset α)) : Prop :=
  HasAtLeastEdgesOnVertices H 4 3

/-- A subgraph on 5 vertices with (at least) 7 edges. -/
abbrev Has5Vertices7Edges {α : Type*} [Fintype α] [DecidableEq α] (H : Finset (Finset α)) : Prop :=
  HasAtLeastEdgesOnVertices H 5 7

/-- Harris's counterexample has exactly 28 edges. -/
@[category test, AMS 5]
theorem harrisCounterexample_card : HarrisCounterexample.card = 28 := by decide +kernel

/-- Harris's counterexample is 3-uniform. -/
@[category test, AMS 5]
theorem harrisCounterexample_is3Uniform : Is3Uniform HarrisCounterexample := by
  unfold Is3Uniform
  decide +kernel

/--
Harris's counterexample has no subgraph on 4 vertices with (at least) 3 edges.

This is the key verification: we check all `choose 9 4 = 126` possible 4-vertex subsets and confirm
each contains at most 2 edges of the hypergraph.
-/
@[category test, AMS 5]
theorem harrisCounterexample_no4Vertices3Edges : ¬Has4Vertices3Edges HarrisCounterexample := by
  unfold Has4Vertices3Edges HasAtLeastEdgesOnVertices
  native_decide

/-- Harris's counterexample also avoids the 5-vertex / 7-edge configuration from the original
statement. -/
@[category test, AMS 5]
theorem harrisCounterexample_no5Vertices7Edges : ¬Has5Vertices7Edges HarrisCounterexample := by
  unfold Has5Vertices7Edges HasAtLeastEdgesOnVertices
  native_decide

/--
**Erdős Problem 794** (Disproved)

It is NOT true that every 3-uniform hypergraph on 3n vertices with n³+1 edges
must contain either:
- a subgraph on 4 vertices with 3 edges, or
- a subgraph on 5 vertices with 7 edges.

Harris's counterexample provides a 3-uniform hypergraph on `9 = 3 * 3` vertices with
`28 = 3 ^ 3 + 1` edges that avoids both forbidden configurations.
-/
@[category research solved, AMS 5]
theorem erdos_794 : answer(False) ↔
    (∀ n : ℕ, ∀ H : Finset (Finset (Fin (3 * n))),
      Is3Uniform H → n ^ 3 + 1 ≤ H.card →
        Has4Vertices3Edges H ∨ Has5Vertices7Edges H) := by
  -- `answer(False)` is `False`, so this is equivalent to `¬ Statement`.
  simp only [false_iff]
  intro h
  have hEdges : (3 ^ 3 + 1 : ℕ) ≤ HarrisCounterexample.card := by
    native_decide
  have hForbid :=
    h 3 HarrisCounterexample harrisCounterexample_is3Uniform hEdges
  cases hForbid with
  | inl h4 => exact harrisCounterexample_no4Vertices3Edges h4
  | inr h5 => exact harrisCounterexample_no5Vertices7Edges h5

end Erdos794
