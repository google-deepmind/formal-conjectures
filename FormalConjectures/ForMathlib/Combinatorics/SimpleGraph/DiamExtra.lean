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

-- Authors: Rida Hamadani

import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!

# Diameter of a simple graph

This module defines the eccentricity of vertices, the diameter, and the radius of a simple graph.

## Main definitions

    * `SimpleGraph.eccent`: the eccentricity of a vertex in a simple graph, which is the maximum
      distances between it and the other vertices.
    * `SimpleGraph.ediam`: the graph extended diameter, which is the maximum eccentricity.
      It is `ℕ∞`-valued.
    * `SimpleGraph.diam`: the graph diameter, an `ℕ`-valued version of `SimpleGraph.ediam`.
    * `SimpleGraph.radius`: the graph radius, which is the minimum eccentricity. It is `ℕ∞`-valued.
    * `SimpleGraph.center`: the set of vertices with eccentricity equal to the graph's radius.

-/

assert_not_exists Field

namespace SimpleGraph
variable {α : Type*} {G G' : SimpleGraph α}

section eccent

/-- The eccentricity of a vertex is the greatest distance between it and any other vertex. -/
noncomputable def eccent (G : SimpleGraph α) (u : α) : ℕ∞ :=
  ⨆ v, G.edist u v

lemma eccent_def : G.eccent = fun u ↦ ⨆ v, G.edist u v := rfl

lemma edist_le_eccent {u v : α} : G.edist u v ≤ G.eccent u :=
  le_iSup (G.edist u) v

lemma exists_edist_eq_eccent_of_finite [Finite α] (u : α) :
    ∃ v, G.edist u v = G.eccent u :=
  have : Nonempty α := Nonempty.intro u
  exists_eq_ciSup_of_finite

lemma eccent_eq_top_of_not_connected (h : ¬ G.Connected) (u : α) :
    G.eccent u = ⊤ := by
  rw [connected_iff_exists_forall_reachable] at h
  push_neg at h
  obtain ⟨v, h⟩ := h u
  rw [eq_top_iff, ← edist_eq_top_of_not_reachable h]
  exact le_iSup (G.edist u) v

lemma eccent_eq_zero_of_subsingleton [Subsingleton α] (u : α) : G.eccent u = 0 := by
  simpa [eccent, edist_eq_zero_iff] using subsingleton_iff.mp ‹_› u

lemma eccent_ne_zero [Nontrivial α] (u : α) : G.eccent u ≠ 0 := by
  obtain ⟨v, huv⟩ := exists_ne ‹_›
  contrapose! huv
  simp only [eccent, ENat.iSup_eq_zero, edist_eq_zero_iff] at huv
  exact (huv v).symm

lemma eccent_eq_zero_iff (u : α) : G.eccent u = 0 ↔ Subsingleton α := by
  refine ⟨fun h ↦ ?_, fun _ ↦ eccent_eq_zero_of_subsingleton u⟩
  contrapose! h
  rw [not_subsingleton_iff_nontrivial] at h
  exact eccent_ne_zero u

lemma eccent_pos_iff (u : α) : 0 < G.eccent u ↔ Nontrivial α := by
  rw [pos_iff_ne_zero, ← not_subsingleton_iff_nontrivial, ← eccent_eq_zero_iff]

@[simp]
lemma eccent_bot [Nontrivial α] (u : α) : (⊥ : SimpleGraph α).eccent u = ⊤ :=
  eccent_eq_top_of_not_connected bot_not_connected u

@[simp]
lemma eccent_top [Nontrivial α] (u : α) : (⊤ : SimpleGraph α).eccent u = 1 := by
  apply le_antisymm ?_ <| Order.one_le_iff_pos.mpr <| pos_iff_ne_zero.mpr <| eccent_ne_zero u
  rw [eccent, iSup_le_iff]
  intro v
  cases eq_or_ne u v <;> simp_all [edist_top_of_ne]

proof_wanted eq_top_iff_forall_eccent_eq_one [Nontrivial α] :
    G = ⊤ ↔ ∀ u, G.eccent u = 1

end eccent

/--
The diameter is the greatest distance between any two vertices. If the graph is disconnected,
this will be `0`.
-/
lemma diam_eq_zero_of_subsingleton [Subsingleton α] : G.diam = 0 := by
  simp [diam, ediam_eq_zero_iff_subsingleton.mpr (by assumption)]

proof_wanted diam_ne_zero [Nontrivial α] : G.diam ≠ 0

lemma nontrivial_of_diam_ne_zero' (h : G.diam ≠ 0) : Nontrivial α := by
  contrapose! h
  rw [not_nontrivial_iff_subsingleton] at h
  exact diam_eq_zero_of_subsingleton

section radius

/-- The radius of a graph is the minimum eccentricity of its vertices. It's `⊤` for the empty
graph. -/
noncomputable def radius (G : SimpleGraph α) : ℕ∞ :=
  ⨅ u, G.eccent u

/-- The center of a graph is the set of vertices with minimum eccentricity. -/
noncomputable def center (G : SimpleGraph α) : Set α :=
  {u | G.eccent u = G.radius}

lemma center_def : G.center = {u | G.eccent u = G.radius} := rfl

lemma radius_le_eccent {u : α} : G.radius ≤ G.eccent u :=
  iInf_le G.eccent u

proof_wanted radius_le_ediam : G.radius ≤ G.ediam

lemma exists_eccent_eq_radius_of_finite [Nonempty α] [Finite α] :
    ∃ u, G.eccent u = G.radius :=
  exists_eq_ciInf_of_finite

lemma center_nonempty_of_finite [Nonempty α] [Finite α] : G.center.Nonempty :=
  exists_eccent_eq_radius_of_finite

proof_wanted diam_le_two_mul_radius (h : G.center.Nonempty) : G.diam ≤ 2 * G.radius

end radius

section Path
open Path

proof_wanted dist_le_diam_of_mem_path {G : SimpleGraph α} {u v : α} (p : G.Walk u v) (w : α)
    (hw : w ∈ p.support) : G.dist w u ≤ G.diam

end Path

end SimpleGraph
