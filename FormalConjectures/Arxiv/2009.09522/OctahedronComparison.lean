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
# Octahedron Comparison in CAT(0) Spaces

*Reference:* [arxiv/2009.09522](https://arxiv.org/abs/2009.09522v4)
**5-point CAT(0) spaces after Tetsu Toyoda**
by **Nina Lebedeva and Anton Petrunin**

A *computer-assisted proof candidate* for the forward direction in the geodesic
case is due to **J. Kim**: *Octahedron comparison in geodesic CAT(0) spaces:
An exact computer-assisted proof candidate*. To our knowledge, it has not yet
been independently checked or published.

Question 6.1 asks whether every length CAT(0) space satisfies octahedron
comparison. The converse asks whether every six-point metric space satisfying
octahedron comparison admits an isometric embedding into a length CAT(0) space.
-/

@[expose] public section
namespace Arxiv.«2009.09522»

open Metric SimpleGraph

/-- The octahedron graph $K_{2,2,2}$. Its vertices are pairs $(i, j)$, and two vertices are
adjacent when their first coordinates differ. -/
def octahedronGraph : SimpleGraph (Fin 3 × Fin 2) where
  Adj u v := u.1 ≠ v.1
  symm.symm _ _ h := Ne.symm h
  loopless.irrefl _ h := h rfl

/-- Question 6.1.1: does every length CAT(0) space satisfy octahedron comparison? -/
@[category research open, question, AMS 51]
theorem lengthCATZero_implies_octahedronComparison (X : Type) [MetricSpace X]
    (hLength : isLengthSpace (X := X)) (hCATZero : isCATZero (X := X)) :
    GraphComparison (X := X) octahedronGraph := by
  sorry

/-- Question 6.1.2: does every six-point metric space that satisfies octahedron
comparison embed isometrically into a length CAT(0) space? -/
@[category research open, question, AMS 51]
theorem octahedronComparison_implies_isometricEmbedding
    (P : Type) [MetricSpace P] [Fintype P]
    (hCard : Fintype.card P = 6)
    (hOct : GraphComparison  (X := P) octahedronGraph) :
    ∃ (Y : Type) (mY : MetricSpace Y),
        Metric.isLengthSpace (X := Y) ∧
        Metric.isCATZero (X := Y) ∧
        ∃ f : P → Y, Isometry f := by
  sorry

end Arxiv.«2009.09522»
