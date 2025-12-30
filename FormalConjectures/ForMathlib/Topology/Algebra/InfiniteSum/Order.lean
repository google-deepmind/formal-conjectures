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
import Mathlib.Topology.Algebra.InfiniteSum.Order

variable {ι α : Type*} [PartialOrder α] [CommGroup α] [IsOrderedMonoid α] [UniformSpace α]
  [IsUniformGroup α] [CompleteSpace α] [OrderClosedTopology α]
  {f : ι → α} {s : Finset ι} {t : Set ι}

@[to_additive]
protected lemma Multipliable.prod_le_tprod_set (hst : ↑s ⊆ t) (hfst : ∀ i ∉ s, i ∈ t → 1 ≤ f i)
    (hf : Multipliable f) : ∏ i ∈ s, f i ≤ ∏' i : t, f i := by
  rw [tprod_subtype, Finset.prod_congr rfl]
  refine (hf.mulIndicator t).prod_le_tprod _ (by simpa [Set.mulIndicator, apply_ite])
  rintro i hi
  simp [Set.mulIndicator, hst hi]
