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
# Erdős Problem 630

*References:*
- [erdosproblems.com/630](https://www.erdosproblems.com/630)
-/

@[expose] public section

open Filter Topology MeasureTheory SimpleGraph

namespace Erdos630

/-- A crossing-free straight-line drawing of a finite graph in the Euclidean plane.
Distinct edges intersect only at shared vertices, and no other vertex lies on an edge. -/
def HasPlanarDrawing {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ p : Fin n → EuclideanSpace ℝ (Fin 2), Function.Injective p ∧
    (∀ a b v, G.Adj a b → p v ∈ segment ℝ (p a) (p b) → v = a ∨ v = b) ∧
    (∀ a b c d, G.Adj a b → G.Adj c d →
      ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
      ∀ x, x ∈ segment ℝ (p a) (p b) → x ∈ segment ℝ (p c) (p d) →
        ∃ v, (v = a ∨ v = b) ∧ (v = c ∨ v = d) ∧ x = p v)

/-- Every finite planar bipartite graph is 3-choosable. Proved by Alon and Tarsi [AlTa92].
For finite simple graphs planarity is equivalent to the existence of a straight-line drawing
(Fáry's theorem). -/
@[category research solved, question, AMS 5]
theorem erdos_630 (n : ℕ) (G : SimpleGraph (Fin n))
    (hp : HasPlanarDrawing G) (hb : G.Colorable 2) : G.listChromaticNumber ≤ 3 := by
  sorry

end Erdos630
