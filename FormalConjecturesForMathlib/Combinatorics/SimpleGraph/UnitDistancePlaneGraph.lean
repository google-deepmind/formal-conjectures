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
module

public import FormalConjecturesForMathlib.Geometry.Euclidean
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]

open Finset List

/-- A unit distance graph in ℝ²:
A graph where the vertices V are a collection of points in ℝ² and there is
an edge between two points if and only if the distance between them is 1. -/
def UnitDistancePlaneGraph (V : Set (EuclideanSpace ℝ (Fin 2))) : SimpleGraph V where
  Adj x y := dist x y = 1
  symm.symm x y := by simp [dist_comm]

/-- An integer distance graph in ℝ²:
the same construction with `1` replaced by an arbitrary positive integer, so two distinct
points are adjacent exactly when the distance between them is a positive whole number. -/
def IntegerDistancePlaneGraph (V : Set (EuclideanSpace ℝ (Fin 2))) : SimpleGraph V where
  Adj x y := ∃ n : ℕ, 0 < n ∧ dist x y = n
  symm.symm x y := by simp [dist_comm]
  loopless.irrefl x := by
    rintro ⟨n, hn, h⟩
    rw [dist_self, eq_comm, Nat.cast_eq_zero] at h
    lia

/-- A distance graph in ℝ² for an arbitrary set `A` of distances:
two distinct points are adjacent exactly when the distance between them is a member of `A`.
The condition `x ≠ y` keeps the graph loopless; it is redundant when `A ⊆ (0, ∞)`. -/
def DistancePlaneGraph (A : Set ℝ) (V : Set (EuclideanSpace ℝ (Fin 2))) : SimpleGraph V where
  Adj x y := x ≠ y ∧ dist x y ∈ A
  symm.symm x y := fun ⟨hne, hd⟩ ↦ ⟨hne.symm, by rw [dist_comm]; exact hd⟩
  loopless.irrefl x := by
    rintro ⟨hne, -⟩
    exact hne rfl

theorem distancePlaneGraph_adj {A : Set ℝ} {V : Set (EuclideanSpace ℝ (Fin 2))} {x y : V} :
    (DistancePlaneGraph A V).Adj x y ↔ x ≠ y ∧ dist x y ∈ A :=
  Iff.rfl

/-- With no allowed distances, the distance graph has no edges. -/
theorem distancePlaneGraph_empty (V : Set (EuclideanSpace ℝ (Fin 2))) :
    DistancePlaneGraph ∅ V = ⊥ := by
  ext x y
  simp [distancePlaneGraph_adj]

/-- With the single allowed distance `1`, the distance graph is the unit distance graph. -/
theorem distancePlaneGraph_singleton_one (V : Set (EuclideanSpace ℝ (Fin 2))) :
    DistancePlaneGraph {1} V = UnitDistancePlaneGraph V := by
  ext x y
  rw [distancePlaneGraph_adj]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.ne, h⟩⟩

open scoped EuclideanGeometry

/-- `G` can be embedded in `ℝ^n` with every edge a unit line segment if there is an injective map
from the vertices of `G` to `ℝ^n` sending any two adjacent vertices to points at distance `1`. -/
def UnitDistanceEmbeddable {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ f : V → ℝ^n, Function.Injective f ∧ ∀ u v : V, G.Adj u v → dist (f u) (f v) = 1

/-- `G` has dimension `n`: the least `m` for which `G` embeds in `ℝ^m` with every edge a unit
line segment. -/
def HasDimension {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  IsLeast {m | UnitDistanceEmbeddable G m} n

end SimpleGraph
