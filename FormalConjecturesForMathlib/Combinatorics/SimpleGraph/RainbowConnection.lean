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

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Nat.Lattice

@[expose] public section

/-!
# Rainbow connection number

This file defines `SimpleGraph.rainbowConnectionNumber`, the minimum number of
colors in a rainbow-connected edge-coloring.
-/

namespace SimpleGraph

variable {α : Type*}

/-- A `k`-edge-coloring `c : Sym2 α → Fin k` is **rainbow-connected** if for every
pair of distinct vertices there is a path (as a `Walk`) whose dart-colors are all
distinct (i.e., the list of colors along the path has no duplicates). -/
def IsRainbowConnected (G : SimpleGraph α) {k : ℕ} (c : Sym2 α → Fin k) : Prop :=
  ∀ u v : α, u ≠ v →
    ∃ p : G.Walk u v, p.IsPath ∧
      List.Nodup (p.darts.map (fun d => c (Sym2.mk d.toProd)))

/-- The **rainbow connection number** `rc(G)`: the minimum number of colors in a
rainbow-connected edge-coloring.  The value `sInf ∅ = 0` in Lean's `sInf`
convention is harmless for disconnected or trivial graphs. -/
noncomputable def rainbowConnectionNumber (G : SimpleGraph α) : ℕ :=
  sInf {k | ∃ c : Sym2 α → Fin k, IsRainbowConnected G c}

end SimpleGraph
