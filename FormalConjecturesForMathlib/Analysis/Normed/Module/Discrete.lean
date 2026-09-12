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

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete

@[expose] public section

open Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A discrete additive subgroup of a real normed space meets the line `ℝ ∙ v` in an infinite
cyclic subgroup. -/
theorem AddSubgroup.exists_inf_span_eq_zmultiples (Λ : AddSubgroup E) [DiscreteTopology Λ]
    {v : E} (hv : v ≠ 0) :
    ∃ w : E, Λ ⊓ (ℝ ∙ v).toAddSubgroup = zmultiples w := by
  set S : AddSubgroup ℝ := Λ.comap (LinearMap.toSpanSingleton ℝ E v)
  have : DiscreteTopology S :=
    (((isClosedEmbedding_smul_left hv).isEmbedding.comp IsEmbedding.subtypeVal).codRestrict
      Λ fun t ↦ t.2).discreteTopology
  obtain ⟨a, ha⟩ := S.isAddCyclic_iff_exists_zmultiples_eq_top.mp
    (discrete_iff_addCyclic.mpr inferInstance)
  refine ⟨a • v, AddSubgroup.ext fun z ↦ ?_⟩
  simp only [mem_inf, Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton, mem_zmultiples_iff]
  have hmemS (t : ℝ) : t ∈ S ↔ t • v ∈ Λ := Iff.rfl
  refine ⟨fun ⟨hz, t, ht⟩ ↦ ?_, fun ⟨n, hn⟩ ↦ ⟨?_, n • a, hn ▸ smul_assoc n a v⟩⟩
  · obtain ⟨n, hn⟩ := mem_zmultiples_iff.mp <| ha ▸ (hmemS t).mpr (ht ▸ hz)
    exact ⟨n, by rwa [← smul_assoc, hn]⟩
  · rw [← hn, ← smul_assoc n a v]
    exact (hmemS _).mp (ha ▸ mem_zmultiples_iff.mpr ⟨n, rfl⟩)
