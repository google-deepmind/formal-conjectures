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
public import FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture146.Reduction
public import FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture146.ExceptionalTheorem

@[expose] public section

/-!
# Written on the Wall II — Conjecture 146

This module proves a theorem with the exact hypotheses and conclusion of the
current Formal Conjectures declaration. The proof combines the general
arithmetic reduction with the kernel-checked exceptional induced-tree theorem.
-/

open Classical
open SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture146.Proof

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Written on the Wall II, Conjecture 146, with the exact upstream signature. -/
theorem conjecture146 (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) (hrad : 0 < (graphSquare G).radius.toNat) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
      largestInducedTreeSize G * (graphSquare G).radius.toNat := by
  exact conjecture146_of_exceptional_case G h hrad (exceptional_case G h)

/-- Compilation guard that restates the upstream declaration verbatim. -/
example (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) (hrad : 0 < (graphSquare G).radius.toNat) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
      largestInducedTreeSize G * (graphSquare G).radius.toNat :=
  WrittenOnTheWallII.GraphConjecture146.Proof.conjecture146 G h hrad


end WrittenOnTheWallII.GraphConjecture146.Proof
