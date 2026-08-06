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

public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Degeneracy of a simple graph

A graph is `r`-degenerate if every induced subgraph has minimum degree at most `r`, equivalently
if every nonempty finite set of vertices contains a vertex with at most `r` neighbours inside that
set. The least such `r` is the *degeneracy* of the graph. Degeneracy is the standard measure of
"uniform sparsity" appearing in extremal graph theory; see e.g. Erdős problem
[#146](https://www.erdosproblems.com/146).

## Main definitions

* `SimpleGraph.IsDegenerate r G`: `G` is `r`-degenerate.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {r : ℕ}

open Classical in
/-- `G.IsDegenerate r` means that `G` is `r`-degenerate: every nonempty finite set `s` of vertices
contains a vertex with at most `r` neighbours inside `s`. Equivalently, every induced subgraph of
`G` has a vertex of degree at most `r`. -/
def IsDegenerate (r : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, {w ∈ s | G.Adj v w}.card ≤ r

/-- `SimpleGraph.IsDegenerate` restated with the ambient decidability instances, so that concrete
instances can be checked by `decide`. -/
lemma isDegenerate_iff_of_decidableRel [DecidableEq V] [DecidableRel G.Adj] :
    G.IsDegenerate r ↔
      ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, (s.filter (G.Adj v)).card ≤ r := by
  simp only [IsDegenerate]
  congr!

end SimpleGraph
