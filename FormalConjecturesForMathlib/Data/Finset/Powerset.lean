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
import Mathlib.Data.Finset.Powerset

namespace Finset
variable {α : Type*} [DecidableEq α] {s t : Finset α} {n : ℕ}

attribute [gcongr] powersetCard_mono

lemma powersetCard_inter : powersetCard n (s ∩ t) = powersetCard n s ∩ powersetCard n t := by
  ext; simpa [subset_inter_iff] using and_and_right

@[simp] lemma disjoint_powersetCard_powersetCard :
    Disjoint (powersetCard n s) (powersetCard n t) ↔ #(s ∩ t) < n := by
  simp [disjoint_iff_inter_eq_empty, ← powersetCard_inter]

end Finset
