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
import FormalConjecturesTest.ForMathlib.Computability.RestrictedGraphProblems

/-! # Axiom audit for bounded-degree graph definitions, helpers, and edge-coloring tests -/

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
#print axioms SimpleGraph.EdgeLabeling.IsProper
#print axioms SimpleGraph.EdgeLabeling.isProper_iff
#print axioms Computability.MatrixGraph.DegreeAtMost
#print axioms Computability.MatrixGraph.DegreeAtMost.mono
#print axioms Computability.MatrixGraph.CubicGraph
#print axioms Computability.MatrixGraph.CubicGraph.degreeAtMost
#print axioms Computability.MatrixGraph.DegreeFourThreeColorable
#print axioms Computability.MatrixGraph.SubcubicVertexCover
#print axioms Computability.MatrixGraph.CubicEdgeThreeColorable
#print axioms Computability.MatrixGraph.CubicHamiltonian
#print axioms Computability.MatrixGraph.SameColorMatching
#print axioms Computability.MatrixGraph.sameColorSubgraph
#print axioms Computability.MatrixGraph.sameColorMatching_iff
#print axioms Computability.MatrixGraph.sameColorMatching_not
#print axioms Computability.MatrixGraph.CubicTwoColorMatching
#print axioms Computability.MatrixGraph.RestrictedTest.completeFourLabels
#print axioms Computability.MatrixGraph.RestrictedTest.completeFour_edgeColorable
#print axioms Computability.MatrixGraph.RestrictedTest.triangleLabels
#print axioms Computability.MatrixGraph.RestrictedTest.triangle_not_edgeTwoColorable
#print axioms Computability.MatrixGraph.RestrictedTest.triangle_edgeThreeColorable
#print axioms Computability.MatrixGraph.RestrictedTest.nonvacuous_machine_interface
