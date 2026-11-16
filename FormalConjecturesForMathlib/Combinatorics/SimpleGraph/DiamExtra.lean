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
module

public import Mathlib.Combinatorics.SimpleGraph.Diam

@[expose] public section

assert_not_exists Field

namespace SimpleGraph
variable {α : Type*} {G G' : SimpleGraph α}

/--
The diameter is the greatest distance between any two vertices. If the graph is disconnected,
this will be `0`.
-/
lemma diam_eq_zero_of_subsingleton [Subsingleton α] : G.diam = 0 := by
  simp [diam, ediam_eq_zero_iff_subsingleton.mpr (by assumption)]

end SimpleGraph
