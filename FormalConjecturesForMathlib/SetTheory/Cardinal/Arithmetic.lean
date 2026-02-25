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
import Mathlib.SetTheory.Cardinal.Arithmetic

namespace Cardinal
variable {α : Type*} {s t : Set α}

@[simp] lemma aleph0_le_mk_set : ℵ₀ ≤ #s ↔ s.Infinite := by
  rw [aleph0_le_mk_iff, Set.infinite_coe_iff]

@[simp]
lemma mk_diff_eq_left' (hs : s.Infinite) (hst : #↑(s ∩ t) < #s) : #↑(s \ t) = #s := by
  refine (mk_le_mk_of_subset Set.diff_subset).eq_of_not_lt
    fun h ↦ (add_lt_of_lt (by simpa) hst h).not_ge ?_
  grw [← mk_union_le .., Set.inter_union_diff]

@[simp]
lemma mk_diff_eq_left (hs : s.Infinite) (hts : #t < #s) : #↑(s \ t) = #s :=
  mk_diff_eq_left' hs <| hts.trans_le' <| mk_subtype_mono Set.inter_subset_right

@[simp]
lemma mk_diff_eq_left_of_finite' (hs : s.Infinite) (hst : (s ∩ t).Finite) : #↑(s \ t) = #s :=
  mk_diff_eq_left' hs <| (aleph0_le_mk_set.2 hs).trans_lt' <| by simpa

@[simp]
lemma mk_diff_eq_left_of_finite (hs : s.Infinite) (ht : t.Finite) : #↑(s \ t) = #s :=
  mk_diff_eq_left hs <| (aleph0_le_mk_set.2 hs).trans_lt' <| by simpa

end Cardinal
