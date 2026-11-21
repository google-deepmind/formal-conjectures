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

public import Mathlib.Data.Finset.Card
public import Std.Data.TreeSet.Lemmas

/-!
# Finite-list cardinality via tree sets

For a transitive comparison function that detects equality, the size of the tree set built
from a list equals the cardinality of the list's finite set.
-/

@[expose] public section

namespace List

/-- A tree set and a finite set built from the same list have the same cardinality. -/
theorem card_to_finset_eq_tree_set_size {α : Type*} [DecidableEq α]
    (l : List α) (cmp : α → α → Ordering) [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :
    l.toFinset.card = (Std.TreeSet.ofList l cmp).size := by
  let t : Std.TreeSet α cmp := Std.TreeSet.ofList l cmp
  have hmem : l.toFinset = t.toList.toFinset := by
    ext x
    simp [t]
  have hnodup : t.toList.Nodup := by
    apply (Std.TreeSet.distinct_toList (t := t)).imp
    intro x y hxy heq
    subst y
    exact hxy Std.ReflCmp.compare_self
  calc
    l.toFinset.card = t.toList.toFinset.card := congrArg Finset.card hmem
    _ = t.toList.length := List.toFinset_card_of_nodup hnodup
    _ = t.size := Std.TreeSet.length_toList

end List
