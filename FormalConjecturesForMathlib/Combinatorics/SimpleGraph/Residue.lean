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
public import Mathlib.Data.Finset.Sort

@[expose] public section

namespace SimpleGraph
open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-!
## Residue
The residue of a graph is the number of zeros remaining after iteratively applying the Havel-Hakimi
algorithm to the degree sequence until all remaining degrees are zero.
-/

/--
Helper function: Performs one step of the Havel-Hakimi reduction on a degree sequence.
Assumes the input list `s` is sorted descending.
Removes the first element `d`, decrements the next `d` elements by 1, and re-sorts the list descending.

Note: when `s` is the list of vertices arising from a simple graph, if the first index is `s` then
the degree list always has length at least `s+1` so this makes sense.
-/
def havelHakimiStep (s : List ℕ) : List ℕ :=
  match s with
  | [] => []
  | d :: rest =>
    -- Split the rest into the part to decrement (first d elements) and the remaining part.
    let (to_decrement, remaining) := rest.splitAt d
    -- Decrement the elements
    let decremented := to_decrement.map (· - 1)
    -- Combine and re-sort descending.
    (decremented ++ remaining).mergeSort (· ≥ ·)

/--
Auxiliary function to calculate the residue recursively.
Applies Havel-Hakimi steps until the sequence consists only of zeros or is empty.
-/
partial def residueAux : List ℕ → ℕ
  | [] => 0        -- Empty sequence, residue is 0.
  | 0 :: s => 1 + s.length -- If the largest degree is 0 (and the list is sorted), all are 0.
  | s => residueAux (havelHakimiStep s) -- Apply one reduction step and recurse.

/--
Computes the residue of a graph G, ,i.e. the number of zeros remaining after iteratively applying the Havel-Hakimi
algorithm to the degree sequence until all remaining degrees are zero.
Starts with the descending degree sequence and applies the Havel-Hakimi process.
-/
noncomputable def residue (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  -- Get the degree sequence sorted in descending order and apply `residueAux`.
  residueAux ((Finset.univ.val.map fun v => G.degree v).sort (· ≥ ·))

end SimpleGraph
