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

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Nat.Lattice

@[expose] public section

/-!
# Odd girth

This file defines `SimpleGraph.oddGirth`, the length of a shortest odd cycle.
-/

namespace SimpleGraph

variable {α : Type*}

open Classical in
/-- The **odd girth** of `G` is the length of a shortest odd-length cycle.
Returns 0 if `G` has no odd cycle (i.e., `G` is bipartite or acyclic). -/
noncomputable def oddGirth (G : SimpleGraph α) : ℕ :=
  let oddCycleLengths := {k | Odd k ∧ ∃ v : α, ∃ w : G.Walk v v, w.IsCycle ∧ w.length = k}
  if oddCycleLengths.Nonempty then sInf oddCycleLengths else 0

end SimpleGraph
