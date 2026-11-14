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
public import Mathlib.Topology.Path
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Crossing-free topological plane embeddings

An edge is an injective path, its interior avoids all vertices, and interiors of
distinct unoriented edges are disjoint.

Adapted from OpenAI's
[BarnetteHamiltonian](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BarnetteHamiltonian.lean),
Apache-2.0. Namespace and imports were changed.
-/

@[expose] public section

namespace SimpleGraph

/-- A crossing-free topological drawing in the plane. -/
structure PlaneEmbedding {V : Type*} (G : SimpleGraph V) where
  point : V → ℝ × ℝ
  point_injective : Function.Injective point
  arc : ∀ v w : V, G.Adj v w → Path (point v) (point w)
  arc_injective : ∀ (v w : V) (h : G.Adj v w), Function.Injective (arc v w h)
  arc_reverse : ∀ (v w : V) (h : G.Adj v w), arc w v h.symm = (arc v w h).symm
  arc_avoids_vertices : ∀ (v w : V) (h : G.Adj v w) (t : unitInterval) (z : V),
    arc v w h t = point z → (t = 0 ∧ z = v) ∨ (t = 1 ∧ z = w)
  interiors_disjoint : ∀ (v w x y : V) (h : G.Adj v w) (k : G.Adj x y)
    (t s : unitInterval), t ≠ 0 → t ≠ 1 → s ≠ 0 → s ≠ 1 →
      arc v w h t = arc x y k s → (v = x ∧ w = y) ∨ (v = y ∧ w = x)

theorem PlaneEmbedding.interior_ne_vertex {V : Type*} {G : SimpleGraph V}
    (e : G.PlaneEmbedding) {v w : V} (h : G.Adj v w) {t : unitInterval}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (z : V) : e.arc v w h t ≠ e.point z := by
  intro heq
  rcases e.arc_avoids_vertices v w h t z heq with h | h
  · exact ht0 h.1
  · exact ht1 h.1

end SimpleGraph
