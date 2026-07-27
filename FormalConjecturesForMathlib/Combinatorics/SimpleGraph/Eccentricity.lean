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

public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Data.Real.Basic
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance

@[expose] public section

namespace SimpleGraph
open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The set of vertices of maximum eccentricity. -/
noncomputable def maxEccentricityVertices (G : SimpleGraph α) : Set α :=
  {v : α | G.eccent v = G.ediam}

/-- The average eccentricity of a graph `G`: the mean of `G.eccent v` over all vertices,
converted to a real number. Returns 0 if the graph has no vertices. -/
noncomputable def averageEccentricity (G : SimpleGraph α) : ℝ :=
  (∑ v : α, (G.eccent v).toNat) / (Fintype.card α : ℝ)

/-- The diameter of a finite graph as a computable natural number: the maximum BFS distance
(`computable_dist`) over all ordered pairs of vertices. -/
def computable_ediam (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup fun p : α × α => computable_dist G p.1 p.2

/-- For a connected finite graph, the extended diameter `ediam` equals the computable diameter. -/
theorem ediam_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] [Nonempty α]
    (hc : G.Connected) : G.ediam = (computable_ediam G : ℕ∞) := by
  apply le_antisymm
  · rw [ediam_le_iff]; intro u v
    rw [← (hc.preconnected u v).coe_dist_eq_edist, dist_eq_computable]
    exact_mod_cast Finset.le_sup (f := fun p : α × α => computable_dist G p.1 p.2) (Finset.mem_univ (u, v))
  · obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (α × α)) Finset.univ_nonempty
      (fun p : α × α => computable_dist G p.1 p.2)
    have hp' : computable_ediam G = computable_dist G p.1 p.2 := hp
    rw [hp', ← dist_eq_computable, (hc.preconnected p.1 p.2).coe_dist_eq_edist]
    exact edist_le_ediam

/-- The eccentricity of a vertex `u` in a finite graph as a computable natural number:
the maximum BFS distance (`computable_dist`) from `u` to any vertex. -/
def computable_eccent (G : SimpleGraph α) [DecidableRel G.Adj] (u : α) : ℕ :=
  Finset.univ.sup fun v => computable_dist G u v

/-- The radius of a finite graph as a computable natural number: the minimum, over all vertices,
of the computable eccentricity. -/
def computable_radius (G : SimpleGraph α) [DecidableRel G.Adj] [Nonempty α] : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (computable_eccent G)

/-- For a connected finite graph, the eccentricity `eccent u` equals the computable eccentricity. -/
theorem eccent_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] [Nonempty α]
    (hc : G.Connected) (u : α) : G.eccent u = (computable_eccent G u : ℕ∞) := by
  apply le_antisymm
  · rw [eccent_le_iff]; intro v
    rw [← (hc.preconnected u v).coe_dist_eq_edist, dist_eq_computable]
    exact_mod_cast Finset.le_sup (f := fun v => computable_dist G u v) (Finset.mem_univ v)
  · obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset α) Finset.univ_nonempty
      (fun v => computable_dist G u v)
    have hv' : computable_eccent G u = computable_dist G u v := hv
    rw [hv', ← dist_eq_computable, (hc.preconnected u v).coe_dist_eq_edist]
    exact edist_le_eccent

/-- For a connected finite graph, the radius `radius` equals the computable radius. -/
theorem radius_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] [Nonempty α]
    (hc : G.Connected) : G.radius = (computable_radius G : ℕ∞) := by
  apply le_antisymm
  · obtain ⟨u0, -, hu0⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty) (computable_eccent G)
    have h0 : computable_radius G = computable_eccent G u0 := hu0
    rw [h0, ← eccent_eq_computable G hc u0]
    exact radius_le_eccent
  · obtain ⟨u1, hu1⟩ := G.exists_eccent_eq_radius
    rw [← hu1, eccent_eq_computable G hc u1]
    exact_mod_cast Finset.inf'_le (computable_eccent G) (Finset.mem_univ u1)

end SimpleGraph
