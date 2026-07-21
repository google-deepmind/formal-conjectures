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
public import FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture146.GlobalBounds

@[expose] public section

/-!
# Arithmetic reduction for WOWII Conjecture 146

This module reduces the complete conjecture to the single exceptional case
formalized separately in issue #4.  The exceptional hypothesis is stated in
exactly the radius-two, diameter-four, periphery-eccentricity-three form used
by that lemma.
-/

open Classical
open SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture146.Proof

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The full Conjecture 146 inequality follows from the sharp exceptional
`(radius, diameter, periphery eccentricity) = (2, 4, 3)` induced-tree bound.

This theorem contains the complete metric and arithmetic integration.  Once
the exceptional theorem is available, the final exact theorem is a one-line
application of this result. -/
theorem conjecture146_of_exceptional_case
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hrad : 0 < (graphSquare G).radius.toNat)
    (hExceptional :
      G.radius.toNat = 2 →
      G.diam = 4 →
      eccSet G (maxEccentricityVertices G : Set α) = 3 →
      6 ≤ largestInducedTreeSize G) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
      largestInducedTreeSize G * (graphSquare G).radius.toNat := by
  set p := eccSet G (maxEccentricityVertices G : Set α)
  set d := G.diam
  set t := largestInducedTreeSize G
  set r := G.radius.toNat
  set rho := (graphSquare G).radius.toNat
  have hrhoPos : 0 < rho := by
    simpa [rho] using hrad
  have hrhoEq : rho = (r + 1) / 2 := by
    simpa [rho, r] using graphSquare_radius_toNat hG
  have hpDiam : p + 1 ≤ d := by
    simpa [p, d] using eccSet_periphery_add_one_le_diam hG
  have hdiamTree : d + 1 ≤ t := by
    simpa [d, t] using diam_succ_le_largestInducedTreeSize hG
  have hdiamRad : d ≤ 2 * r := by
    simpa [d, r] using diam_le_two_mul_radius_toNat hG
  by_cases hrhoTwo : 2 ≤ rho
  · have hpt : p ≤ t := by omega
    calc
      2 * p ≤ 2 * t := Nat.mul_le_mul_left 2 hpt
      _ ≤ rho * t := Nat.mul_le_mul_right t hrhoTwo
      _ = t * rho := Nat.mul_comm _ _
  · have hrhoOne : rho = 1 := by omega
    have hrLeTwo : r ≤ 2 := by omega
    have hdLeFour : d ≤ 4 := by omega
    have hpLeThree : p ≤ 3 := by omega
    by_cases hpTwo : p ≤ 2
    · have hsmall : 2 * p ≤ t := by omega
      simpa [hrhoOne] using hsmall
    · have hpEq : p = 3 := by omega
      have hdEq : d = 4 := by omega
      have hrEq : r = 2 := by omega
      have htSix : 6 ≤ t := by
        simpa [r, d, p, t] using
          hExceptional (by simpa [r] using hrEq)
            (by simpa [d] using hdEq)
            (by simpa [p] using hpEq)
      have hcorner : 2 * p ≤ t := by omega
      simpa [hrhoOne] using hcorner


end WrittenOnTheWallII.GraphConjecture146.Proof
