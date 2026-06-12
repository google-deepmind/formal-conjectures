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

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Tactic.Ring.Basic
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance

@[expose] public section

namespace SimpleGraph
open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Auxiliary function for Szeged index: counts vertices closer to u than v. -/
noncomputable def szeged_aux (G : SimpleGraph α) (u v : α) : ℕ :=
  (Finset.univ.filter (fun w => G.edist w u < G.edist w v)).card

/-- The Szeged index of `G`.

This is define as the sum `∑_{uv ∈ E(G)} n_u(u,v) * n_v(u,v)` where
`n_u(uv)` is the number of vertices closer to `u` than `v`.
-/
noncomputable def szegedIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => szeged_aux G u v * szeged_aux G v u, by simp [mul_comm]⟩

    /-- Computable Szeged auxiliary: count vertices closer to u than v. -/
def computable_szeged_aux (G : SimpleGraph α) [DecidableRel G.Adj] (u v : α) : ℕ :=
  (Finset.univ.filter (fun w => computable_dist G w u < computable_dist G w v)).card

/-- Computable Szeged index. -/
def computable_szeged_index (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ e ∈ G.edgeFinset,
    Sym2.lift ⟨fun u v => computable_szeged_aux G u v * computable_szeged_aux G v u,
      fun a b => by ring⟩ e

-- Helper: edist comparison ↔ dist comparison for adjacent endpoints
omit [Fintype α] [DecidableEq α] in
private lemma edist_lt_iff_dist_lt (G : SimpleGraph α) {u v : α} (hadj : G.Adj u v) (w : α) :
    G.edist w u < G.edist w v ↔ G.dist w u < G.dist w v := by
  by_cases hru : G.Reachable w u
  · have hrv : G.Reachable w v := hru.trans hadj.reachable
    rw [← hru.coe_dist_eq_edist, ← hrv.coe_dist_eq_edist, ENat.coe_lt_coe]
  · have hrv : ¬G.Reachable w v :=
      fun h => hru (h.trans hadj.symm.reachable)
    simp [edist_eq_top_of_not_reachable hru, edist_eq_top_of_not_reachable hrv,
          dist_eq_zero_of_not_reachable hru, dist_eq_zero_of_not_reachable hrv]

private lemma szeged_aux_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj]
    {u v : α} (hadj : G.Adj u v) :
    szeged_aux G u v = computable_szeged_aux G u v := by
  unfold szeged_aux computable_szeged_aux
  congr 1; ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [edist_lt_iff_dist_lt G hadj w, dist_eq_computable, dist_eq_computable]

theorem szeged_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] :
    szegedIndex G = computable_szeged_index G := by
  unfold szegedIndex computable_szeged_index
  apply Finset.sum_congr rfl
  intro e he
  revert he
  refine Sym2.ind (fun u v => ?_) e
  intro he
  simp only [Sym2.lift_mk]
  have hadj : G.Adj u v := by rwa [mem_edgeFinset, mem_edgeSet] at he
  congr 1
  · exact szeged_aux_eq_computable G hadj
  · exact szeged_aux_eq_computable G hadj.symm

end SimpleGraph
