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
import Mathlib.Topology.Algebra.InfiniteSum.Group

open Filter
open scoped Topology

variable {ι α β : Type*} [CommGroup α] [TopologicalSpace α] [IsTopologicalGroup α]
  {f : β → α} {l : Filter ι} {s : ι → Set β}

@[to_additive]
lemma Multipliable.tendsto_tprod_one (hf : Multipliable f) (hs : ∀ b, ∀ᶠ i in l, b ∉ s i) :
    Tendsto (fun i ↦ ∏' b : s i, f b) l (𝓝 1) := by
  rw [tendsto_iff_eventually]
  rintro p hp
  obtain ⟨t, ht⟩ := hf.tprod_vanishing hp
  filter_upwards [t.eventually_all.2 fun b _ ↦ hs b] with i hi
  exact ht _ <| by simpa [Set.disjoint_right]
