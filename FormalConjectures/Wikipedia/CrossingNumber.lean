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
# Crossing numbers of complete and complete bipartite graphs

The crossing number of a graph is the least number of crossing points over its drawings in the
plane. A drawing places the vertices at distinct points and each edge along an injective path
between its endpoints that avoids the other vertices. Distinct edges meet in finitely many
crossing points, each a transversal crossing of exactly two edges.

**Hill's conjecture** [HH63]: the crossing number of $K_n$ is
$$H(n) = \frac14 \left\lfloor\frac n2\right\rfloor \left\lfloor\frac{n-1}2\right\rfloor
  \left\lfloor\frac{n-2}2\right\rfloor \left\lfloor\frac{n-3}2\right\rfloor.$$
It was known for $n \le 12$ [PR07].

**Zarankiewicz's conjecture** [Za54]: the crossing number of $K_{m,n}$ is
$$Z(m, n) = \left\lfloor\frac m2\right\rfloor \left\lfloor\frac{m-1}2\right\rfloor
  \left\lfloor\frac n2\right\rfloor \left\lfloor\frac{n-1}2\right\rfloor.$$
It was known for $\min(m, n) \le 6$ [Kl70].

In both cases a drawing with exactly this number of crossings was known; the conjectures are the
matching lower bounds.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Crossing_number_(graph_theory))
- [Za54] K. Zarankiewicz, *On a problem of P. Turán concerning graphs*, Fund. Math. 41 (1954),
  137–145.
- [HH63] F. Harary and A. Hill, *On the number of crossings in a complete graph*,
  Proc. Edinburgh Math. Soc. (2) 13 (1963), 333–338.
- [Kl70] D. J. Kleitman, *The crossing number of $K_{5,n}$*, J. Combin. Theory 9 (1970),
  315–323.
- [PR07] S. Pan and R. B. Richter, *The crossing number of $K_{11}$ is 100*, J. Graph Theory 56
  (2007), 128–134.
- [OAI26a] OpenAI, *The crossing number of complete graphs*. OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-graphs-September-23-2026/paper.pdf
- [OAI26b] OpenAI, *The crossing number of complete bipartite graphs*. OpenAI Math Release
  preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026/paper.pdf
-/

@[expose] public section

noncomputable section

namespace CrossingNumber

/-- The Euclidean plane. -/
abbrev Plane := ℝ × ℝ

/-- A simple graph with labelled edges: each edge has a source and a target, there are no loops
and no parallel edges. -/
structure Graph (Vertex Edge : Type) where
  /-- The source of an edge. -/
  src : Edge → Vertex
  /-- The target of an edge. -/
  dst : Edge → Vertex
  loopless : ∀ edge, src edge ≠ dst edge
  simple : ∀ edge other, ((src edge = src other ∧ dst edge = dst other) ∨
    (src edge = dst other ∧ dst edge = src other)) → edge = other

/-- The edges `{i, j}` with `i < j` of the complete graph on `Fin order`. -/
abbrev CompleteEdge (order : ℕ) := {pair : Fin order × Fin order // pair.1 < pair.2}

/-- The complete graph `K_order`. -/
def Graph.complete (order : ℕ) : Graph (Fin order) (CompleteEdge order) where
  src edge := edge.val.1
  dst edge := edge.val.2
  loopless edge := ne_of_lt edge.property
  simple edge other same := by
    rcases same with same | reversed
    · exact Subtype.ext (Prod.ext same.1 same.2)
    · have increasing := edge.property
      have other_increasing := other.property
      rw [reversed.1, reversed.2] at increasing
      exact (lt_asymm increasing other_increasing).elim

/-- The complete bipartite graph `K_{m,n}`: the edge `(i, j)` joins `inl i` to `inr j`. -/
def Graph.completeBipartite (m n : ℕ) : Graph (Fin m ⊕ Fin n) (Fin m × Fin n) where
  src edge := .inl edge.1
  dst edge := .inr edge.2
  loopless _ := Sum.inl_ne_inr
  simple edge other same := by
    rcases same with ⟨h₁, h₂⟩ | ⟨h₁, -⟩
    · exact Prod.ext (Sum.inl_injective h₁) (Sum.inr_injective h₂)
    · exact absurd h₁ Sum.inl_ne_inr

variable {Vertex Edge : Type}

/-- A drawing of `graph` in the plane: injective vertex positions and, for each edge, an
injective path between its endpoints whose interior avoids every vertex. -/
structure ContinuousDrawing (graph : Graph Vertex Edge) where
  /-- The position of a vertex. -/
  vertex : Vertex → Plane
  vertex_injective : Function.Injective vertex
  /-- The path drawing an edge. -/
  edge : ∀ edge : Edge, Path (vertex (graph.src edge)) (vertex (graph.dst edge))
  edge_injective : ∀ selected, Function.Injective (edge selected)
  interior_avoids_vertices : ∀ selected time, time ∈ Set.Ioo (0 : unitInterval) 1 →
    ∀ other, edge selected time ≠ vertex other

variable {graph : Graph Vertex Edge}

/-- The drawn edge without its endpoints. -/
def edgeInterior (drawing : ContinuousDrawing graph) (edge : Edge) : Set Plane :=
  drawing.edge edge '' Set.Ioo (0 : unitInterval) 1

/-- `first` and `second` cross transversally at `point`: near `point` a homeomorphic chart
carries them to the two coordinate axes. -/
structure ProperCrossing (first second : Set Plane) (point : Plane) : Prop where
  chart_exists : ∃ chart : OpenPartialHomeomorph Plane Plane,
    point ∈ chart.source ∧ chart point = (0, 0) ∧
    chart '' (chart.source ∩ first) = chart.target ∩ {image | image.2 = 0} ∧
    chart '' (chart.source ∩ second) = chart.target ∩ {image | image.1 = 0}

/-- The points where two distinct edges meet. -/
def crossingPoints (drawing : ContinuousDrawing graph) : Set Plane :=
  {point | ∃ edge other : Edge, edge ≠ other ∧
    point ∈ edgeInterior drawing edge ∧ point ∈ edgeInterior drawing other}

/-- A drawing with finitely many crossing points, each a transversal crossing of exactly two
edges. -/
structure AdmissibleDrawing (graph : Graph Vertex Edge) extends ContinuousDrawing graph where
  crossings_finite : (crossingPoints toContinuousDrawing).Finite
  crossings_proper : ∀ edge other, edge ≠ other → ∀ point,
    point ∈ edgeInterior toContinuousDrawing edge →
    point ∈ edgeInterior toContinuousDrawing other →
    ProperCrossing (edgeInterior toContinuousDrawing edge)
      (edgeInterior toContinuousDrawing other) point
  no_triples : ∀ first second third, first ≠ second → first ≠ third → second ≠ third →
    edgeInterior toContinuousDrawing first ∩ edgeInterior toContinuousDrawing second ∩
      edgeInterior toContinuousDrawing third = ∅

/-- The number of crossing points of a drawing. -/
def crossingCount (drawing : AdmissibleDrawing graph) : ℕ :=
  drawing.crossings_finite.toFinset.card

/-- The crossing number of `graph`: the least number of crossing points of an admissible
drawing. If `graph` has no admissible drawing (for instance, if it has too many vertices to place
injectively in the plane), this is `sInf ∅ = 0`; complete and complete bipartite graphs on
finitely many vertices have admissible drawings. -/
def ordinaryCrossingNumber (graph : Graph Vertex Edge) : ℕ :=
  sInf (Set.range (@crossingCount Vertex Edge graph))

/-- Hill's number `H(n) = ⌊n/2⌋ ⌊(n-1)/2⌋ ⌊(n-2)/2⌋ ⌊(n-3)/2⌋ / 4`. -/
def hill (order : ℕ) : ℕ :=
  (order / 2 * ((order - 1) / 2) * ((order - 2) / 2) * ((order - 3) / 2)) / 4

/-- `⌊r/2⌋ ⌊(r-1)/2⌋`, so that `Z(m, n) = axisPairs m * axisPairs n`. -/
def axisPairs (r : ℕ) : ℕ := (r / 2) * ((r - 1) / 2)

set_option linter.style.formal_proof_palomar false in
/--
**Hill's conjecture** [HH63]: the crossing number of $K_n$ is $H(n)$ for $n \ge 3$.

This was proved by an internal OpenAI model in September 2026 [OAI26a]; see the linked Lean
proof.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CompleteCrossing/Main.lean#L76"]
theorem hill_conjecture (n : ℕ) (hn : 3 ≤ n) :
    ordinaryCrossingNumber (Graph.complete n) = hill n := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
**Zarankiewicz's conjecture** [Za54]: the crossing number of $K_{m,n}$ is $Z(m, n)$.

This was proved by an internal OpenAI model in September 2026 [OAI26b]; see the linked Lean
proof.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Crossing/Main.lean#L8"]
theorem zarankiewicz_conjecture (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ordinaryCrossingNumber (Graph.completeBipartite m n) = axisPairs m * axisPairs n := by
  sorry

/-- `H(5) = 1`, `H(6) = 3`, `H(7) = 9`, `H(8) = 18` and `H(12) = 150`. -/
@[category test, AMS 5]
theorem hill_small : hill 5 = 1 ∧ hill 6 = 3 ∧ hill 7 = 9 ∧ hill 8 = 18 ∧ hill 12 = 150 := by
  decide

/-- `Z(3, 3) = 1`: $K_{3,3}$ is not planar but has a drawing with one crossing. -/
@[category test, AMS 5]
theorem axisPairs_three_mul_three : axisPairs 3 * axisPairs 3 = 1 := by
  decide

end CrossingNumber

end
