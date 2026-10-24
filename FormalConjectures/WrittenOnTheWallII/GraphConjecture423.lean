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

public import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 423

References:
- [E. DeLaVina, Written on the Wall II](http://cms.uhd.edu/faculty/delavinae/research/wowII/open.html),
  entry 423, dated 8 December 2010.
- J. J. Gebendorfer, *Independent Domination Across a Vertex Cut and a Resolution of
  WOWII Conjecture 423*, 1 September 2026, Theorem 1.1 and its corollary.
  [Full source and frozen source records](https://github.com/user-attachments/files/33373559/Gebendorfer_WOWII_423_Intake_2026-10-13.zip).

The surviving HTML has a blank comparison glyph. These statements use the recovered
non-strict upper-bound reading: the reverse direction fails on K4, and strict `<`
fails on the equality family. This source reconstruction is not hidden by formalization.
`N` is the literal closed neighborhood; `internalEdges` counts both endpoints in `M`.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture423

open SimpleGraph

/-- Gebendorfer's stronger cut theorem, valid without connectedness whenever an edge crosses
from `A` to its complement. The `+ 1` form is equivalent to subtracting one on the right. -/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/a76806d654092689138c922a8b62ca7bebf3253b/Proofs/WOWII423Proof.lean"]
theorem cut_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) {a b : V}
    (ha : a ∈ A) (hb : b ∉ A) (hab : G.Adj a b) :
    let N := Finset.univ.filter fun v => v ∈ A ∨ ∃ a ∈ A, G.Adj a v
    G.indepDominationNumber + 1 ≤ (G.induce (N : Set V)).indepNum +
      (G.induce ((Finset.univ \ A : Finset V) : Set V)).indepNum := by
  sorry

/-- WOWII 423: the product bound involving minimum-degree vertices `A`, maximum-degree
vertices `M`, and the closed neighborhood `N`. The regular case is included. -/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/a76806d654092689138c922a8b62ca7bebf3253b/Proofs/WOWII423Proof.lean"]
theorem conjecture423 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hn : 3 < Fintype.card V) :
    let A := Finset.univ.filter fun v => G.degree v = G.minDegree
    let M := Finset.univ.filter fun v => G.degree v = G.maxDegree
    let N := Finset.univ.filter fun v => v ∈ A ∨ ∃ a ∈ A, G.Adj a v
    G.indepDominationNumber ≤ (G.internalEdges M).card +
      (G.induce (N : Set V)).indepNum *
      (G.induce ((Finset.univ \ A : Finset V) : Set V)).indepNum := by
  sorry

end WrittenOnTheWallII.GraphConjecture423
