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
