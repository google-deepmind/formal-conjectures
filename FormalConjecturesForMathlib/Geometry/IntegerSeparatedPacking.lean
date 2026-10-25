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

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import FormalConjecturesForMathlib.Data.Real.NearestInt

/-!
# Points whose distances avoid integers
-/

@[expose] public section

open Metric

/--
`N X δ` is the maximum number of points in a closed disc of radius `X` in the plane such that
the distance between any two of them is at least `δ` away from the nearest integer.
The cardinality supremum is zero if it is unbounded, as happens when `δ = 0` and `X > 0`.
-/
noncomputable def integerSeparatedPackingNumber (X δ : ℝ) : ℕ :=
  sSup {n | ∃ (c : EuclideanSpace ℝ (Fin 2)) (P : Finset (EuclideanSpace ℝ (Fin 2))),
    P.card = n ∧ ↑P ⊆ closedBall c X ∧
      (P : Set (EuclideanSpace ℝ (Fin 2))).Pairwise fun x y => δ ≤ distToNearestInt (dist x y)}
