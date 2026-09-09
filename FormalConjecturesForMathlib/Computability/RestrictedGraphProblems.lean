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

public import FormalConjecturesForMathlib.Computability.MatrixGraphProblems
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Bounded-degree graph decision problems

Matrix inputs use the explicit, square, symmetric, loopless representation in MatrixGraph.
Degree bounds use Mathlib's degree, and cubic means every vertex has degree exactly three.

References:
- Garey, Johnson, and Stockmeyer, *Some simplified NP-complete graph problems* (1976),
  Theorems 2.3 and 2.6, https://doi.org/10.1016/0304-3975(76)90059-1.
- Holyer, *The NP-Completeness of Edge-Coloring* (1981), §4,
  https://doi.org/10.1137/0210055.
- Garey, Johnson, and Tarjan, *The Planar Hamiltonian Circuit Problem is NP-Complete*
  (1976), pp. 704–705, https://doi.org/10.1137/0205049.
- Schaefer, *The Complexity of Satisfiability Problems* (1978), p. 217 and Theorem 7.1,
  https://doi.org/10.1145/800133.804350.
- Demaine, Karntikoon, and Pitimanaaree, *2-Colorable Perfect Matching is NP-complete in
  2-Connected 3-Regular Planar Graphs* (2025), Theorem 3,
  https://doi.org/10.1007/s00224-025-10221-2.

The predicates below impose degree restrictions, not planarity or connectivity.
Finite decidability is by exhaustive search, not an efficient algorithm.
-/

@[expose] public section

namespace SimpleGraph.EdgeLabeling

variable {V K : Type*} {G : SimpleGraph V}

/-- Incident edges have distinct labels. Edges are unordered in Mathlib's EdgeLabeling. -/
def IsProper (c : G.EdgeLabeling K) : Prop :=
  ∀ v, Function.Injective (fun w : G.neighborSet v ↦ c.get v w.1 w.2)

instance [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [DecidableEq K]
    (c : G.EdgeLabeling K) :
    Decidable c.IsProper := by
  unfold IsProper Function.Injective
  infer_instance

/-- Properness is exactly inequality of labels on distinct edges at each vertex. -/
theorem isProper_iff (c : G.EdgeLabeling K) :
    c.IsProper ↔ ∀ v w z (hw : G.Adj v w) (hz : G.Adj v z), w ≠ z →
      c.get v w hw ≠ c.get v z hz := by
  constructor
  · intro h v w z hw hz hne he
    exact hne (congrArg Subtype.val (h v (a₁ := ⟨w, hw⟩) (a₂ := ⟨z, hz⟩) he))
  · intro h v w z he
    apply Subtype.ext
    by_contra hne
    exact h v w.1 z.1 w.2 z.2 hne he

end SimpleGraph.EdgeLabeling

namespace Computability.MatrixGraph

/-- Every vertex has degree at most the supplied bound. -/
def DegreeAtMost (a : Code) (d : ℕ) : Prop :=
  ∀ v : Fin a.length, (toGraph a).degree v ≤ d

instance (a : Code) (d : ℕ) : Decidable (DegreeAtMost a d) := by
  unfold DegreeAtMost
  infer_instance

theorem DegreeAtMost.mono {a : Code} {d e : ℕ} (h : DegreeAtMost a d) (hde : d ≤ e) :
    DegreeAtMost a e :=
  fun v ↦ (h v).trans hde

/-- A valid simple graph with every degree exactly three. The empty graph is vacuously cubic. -/
def CubicGraph (a : Code) : Prop :=
  ValidGraph a ∧ (toGraph a).IsRegularOfDegree 3

instance (a : Code) : Decidable (CubicGraph a) := by
  unfold CubicGraph SimpleGraph.IsRegularOfDegree
  infer_instance

theorem CubicGraph.degreeAtMost {a : Code} (h : CubicGraph a) : DegreeAtMost a 3 :=
  fun v ↦ (h.2 v).le

/-- A proper three-vertex-coloring of a graph with maximum degree at most four. -/
def DegreeFourThreeColorable (a : Code) : Prop :=
  DegreeAtMost a 4 ∧ Colorable (a, 3)

/-- A vertex cover of size at most the positive input bound in a subcubic graph. -/
def SubcubicVertexCover (input : Code × ℕ) : Prop :=
  DegreeAtMost input.1 3 ∧ VertexCover input

/-- A cubic graph whose edges admit a proper coloring with three colors. -/
def CubicEdgeThreeColorable (a : Code) : Prop :=
  CubicGraph a ∧ ∃ c : (toGraph a).EdgeLabeling (Fin 3), c.IsProper

/-- A cubic graph with a spanning cycle of length at least three. -/
def CubicHamiltonian (a : Code) : Prop :=
  CubicGraph a ∧ UndirectedHamiltonian a

/-- Each vertex has exactly one neighbor of its own color. This is not a proper coloring. -/
def SameColorMatching (a : Code) (color : Fin a.length → Bool) : Prop :=
  ∀ v, ∃! w, (toGraph a).Adj v w ∧ color w = color v

instance (a : Code) (color : Fin a.length → Bool) : Decidable (SameColorMatching a color) := by
  unfold SameColorMatching ExistsUnique
  infer_instance

/-- The spanning subgraph consisting of edges whose endpoints have the same color. -/
def sameColorSubgraph (a : Code) (color : Fin a.length → Bool) : (toGraph a).Subgraph where
  verts := Set.univ
  Adj v w := (toGraph a).Adj v w ∧ color w = color v
  adj_sub := And.left
  edge_vert := fun _ ↦ Set.mem_univ _
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩

/-- The monochromatic edges form a perfect matching exactly when each vertex has one partner. -/
theorem sameColorMatching_iff (a : Code) (color : Fin a.length → Bool) :
    SameColorMatching a color ↔ (sameColorSubgraph a color).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  rfl

theorem sameColorMatching_not (a : Code) (color : Fin a.length → Bool) :
    SameColorMatching a (fun v ↦ !(color v)) ↔ SameColorMatching a color := by
  simp [SameColorMatching]

/-- Schaefer's two-colorable perfect-matching problem restricted to cubic graphs. -/
def CubicTwoColorMatching (a : Code) : Prop :=
  CubicGraph a ∧ ∃ color : Fin a.length → Bool, SameColorMatching a color

instance (a : Code) : Decidable (DegreeFourThreeColorable a) := by
  unfold DegreeFourThreeColorable
  infer_instance

instance (input : Code × ℕ) : Decidable (SubcubicVertexCover input) := by
  unfold SubcubicVertexCover
  infer_instance

instance (a : Code) : Decidable (CubicEdgeThreeColorable a) := by
  unfold CubicEdgeThreeColorable
  infer_instance

instance (a : Code) : Decidable (CubicHamiltonian a) := by
  unfold CubicHamiltonian
  infer_instance

instance (a : Code) : Decidable (CubicTwoColorMatching a) := by
  unfold CubicTwoColorMatching
  infer_instance

end Computability.MatrixGraph
