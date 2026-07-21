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
public import Mathlib.Data.Multiset.Interval
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Degrees

@[expose] public section

namespace SimpleGraph
open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The annihilation number of a graph. This is the largest number of degrees that can be added
together without going over the total number of edges of that graph. -/
def annihilationNumber (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  -- Calculate the limit: The number of edges (Sum of degrees / 2)
  letI limit := G.edgeFinset.card

  -- The set of all multisets of degrees that sum to less than or equal to `limit`
  Finset.Iic (degreeMultiset G)
    |>.filter (fun S ↦ Multiset.sum S ≤ limit)
    |>.sup Multiset.card

/--
Computes the annihilation number of a graph G.

It calculates the degree sequence, sorts it ascendingly, and finds the largest prefix length 'k'
(where `0 ≤ k ≤ |V(G)|`) such that the sum of the prefix is less than or equal to the sum of the corresponding suffix.
-/
noncomputable def annihilationNumber' (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  -- 1. Get the degree sequence sorted in ascending order.
  -- G.degree_list returns the list of degrees.
  letI degrees := (Finset.univ.val.map fun v => G.degree v).sort (· ≤ ·)

  -- 2. Define the condition for the annihilation number.
  -- k represents the number of smallest degrees considered (the length of the prefix).
  letI condition (k : ℕ) : Bool := (degrees.take k).sum ≤ (degrees.drop k).sum

  -- 3. Find the maximum k in {0, ..., n} satisfying the condition.
  -- List.range (n + 1) generates the list [0, 1, ..., n].
  letI candidates := (List.range (Fintype.card α + 1)).filter condition

  -- 4. Return the maximum candidate.
  -- The list of candidates is guaranteed to be non-empty because k=0 always satisfies
  -- the condition (0 ≤ sum of all degrees).
  candidates.getLast!

set_option linter.unusedSectionVars false in
-- TODO(Paul-Lez): debug the issue with the unused variable linter...
proof_wanted annihilationNumberEq (G : SimpleGraph α) [DecidableRel G.Adj] :
    annihilationNumber G = annihilationNumber' G

end SimpleGraph
