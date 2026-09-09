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
import FormalConjecturesTest.ForMathlib.Computability.NetworkProblems

/-! # Transitive axiom audit of network definitions and proofs -/

#print axioms ComplexityTheory.HasPolyTimeDecider
#print axioms ComplexityTheory.hasPolyTimeDecider_congr
#print axioms ComplexityTheory.IsPolyTime.hasPolyTimeDecider
#print axioms Computability.MatrixGraph.Code
#print axioms Computability.MatrixGraph.entry
#print axioms Computability.MatrixGraph.Square
#print axioms Computability.MatrixGraph.encoded_row_length
#print axioms Computability.MatrixGraph.encoded_matrix_length
#print axioms Computability.MatrixGraph.encoded_square_length
#print axioms Computability.MatrixGraph.ValidDigraph
#print axioms Computability.MatrixGraph.ValidGraph
#print axioms Computability.MatrixGraph.toDigraph
#print axioms Computability.MatrixGraph.toGraph
#print axioms Computability.MatrixGraph.toGraph_adj
#print axioms Computability.MatrixGraph.Clique
#print axioms Computability.MatrixGraph.VertexCover
#print axioms Computability.MatrixGraph.Colorable
#print axioms Computability.MatrixGraph.colorable_iff
#print axioms Computability.MatrixGraph.next
#print axioms Computability.MatrixGraph.HasSpanningCycle
#print axioms Computability.MatrixGraph.DirectedHamiltonian
#print axioms Computability.MatrixGraph.UndirectedHamiltonian
#print axioms SimpleGraph.decidableIsTree
#print axioms Computability.NetworkProblems.DirectedCycle
#print axioms Computability.NetworkProblems.DirectedCycle.length_le
#print axioms Computability.NetworkProblems.HitsVertexCycles
#print axioms Computability.NetworkProblems.hitsVertexCycles_iff
#print axioms Computability.NetworkProblems.arcs
#print axioms Computability.NetworkProblems.HitsArcCycles
#print axioms Computability.NetworkProblems.hitsArcCycles_iff
#print axioms Computability.NetworkProblems.FeedbackVertexSet
#print axioms Computability.NetworkProblems.FeedbackArcSet
#print axioms Computability.NetworkProblems.weight
#print axioms Computability.NetworkProblems.WeightMatrix
#print axioms Computability.NetworkProblems.selectedGraph
#print axioms Computability.NetworkProblems.SelectedEdges
#print axioms Computability.NetworkProblems.SteinerInput
#print axioms Computability.NetworkProblems.SteinerTree
#print axioms Computability.NetworkProblems.TourMatrix
#print axioms Computability.NetworkProblems.tourCost
#print axioms Computability.NetworkProblems.TravelingSalesman
#print axioms Computability.NetworkProblems.ValidPairs
#print axioms Computability.NetworkProblems.ConnectsIn
#print axioms Computability.NetworkProblems.connectsIn_iff_exists_path
#print axioms Computability.NetworkProblems.DisjointConnectingPaths
#print axioms Computability.NetworkProblems.Test.nonvacuous_machine_interface
