/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjectures.Util.ProblemImports

/-!
# Testing Graph Invariants

This file contains tests for graph invariants on 5 specific concrete graphs:
1. `HouseGraph`: A graph on 5 vertices.
2. `K4`: The complete graph on 4 vertices.
3. `PetersenGraph`: The Petersen graph on 10 vertices.
4. `C6`: The cycle graph on 6 vertices.
5. `Star5`: The star graph with 5 leaves (6 vertices total).

Tests cover:
independence_number, dominationNumber, average_distance, diameter, radius,
girth, order, size, szeged_index, wiener_index, min_degree, max_degree,
average_degree, matching_number, residue, annihilation_number, cvetkovic.
-/

open SimpleGraph

/-! ### Graph Definitions -/

/-- House Graph: Square 0-1-2-3-0 with roof 4 connected to 2,3. -/
def HouseGraph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet {
    s(0, 1), s(1, 2), s(2, 3), s(3, 0),
    s(2, 4), s(3, 4)
  }
instance : DecidableRel HouseGraph.Adj := by unfold HouseGraph; infer_instance

/-- K4: Complete graph on 4 vertices. -/
def K4 : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet {
    s(0, 1), s(0, 2), s(0, 3),
    s(1, 2), s(1, 3),
    s(2, 3)
  }
instance : DecidableRel K4.Adj := by unfold K4; infer_instance

/-- Petersen Graph on 10 vertices. -/
def PetersenGraph : SimpleGraph (Fin 10) :=
  SimpleGraph.fromEdgeSet {
    -- Outer Cycle
    s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0),
    -- Spokes
    s(0, 5), s(1, 6), s(2, 7), s(3, 8), s(4, 9),
    -- Inner Star
    s(5, 7), s(7, 9), s(9, 6), s(6, 8), s(8, 5)
  }
instance : DecidableRel PetersenGraph.Adj := by unfold PetersenGraph; infer_instance

/-- C6: Cycle graph on 6 vertices. -/
def C6 : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet {
    s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 5), s(5, 0)
  }
instance : DecidableRel C6.Adj := by unfold C6; infer_instance

/-- Star5: Star graph with center 0 and 5 leaves. -/
def Star5 : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet {
    s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(0, 5)
  }
instance : DecidableRel Star5.Adj := by unfold Star5; infer_instance


/-! ### House Graph Tests -/

@[category test, AMS 5]
theorem house_indep : a HouseGraph = 2 := by sorry

@[category test, AMS 5]
theorem house_dom : dominationNumber HouseGraph = 2 := by sorry

@[category test, AMS 5]
theorem house_avg_dist : averageDistance HouseGraph = 7/5 := by sorry

@[category test, AMS 5]
theorem house_diameter : maxEccentricity HouseGraph = 2 := by sorry

@[category test, AMS 5]
theorem house_radius : minEccentricity HouseGraph = 2 := by sorry

@[category test, AMS 5]
theorem house_girth : HouseGraph.girth = 3 := by sorry

@[category test, AMS 5]
theorem house_order : n HouseGraph = 5 := by sorry

@[category test, AMS 5]
theorem house_size : HouseGraph.edgeFinset.card = 6 := by sorry

@[category test, AMS 5]
theorem house_szeged : szegedIndex HouseGraph = 24 := by sorry

@[category test, AMS 5]
theorem house_wiener : wienerIndex HouseGraph = 14 := by sorry

@[category test, AMS 5]
theorem house_min_deg : HouseGraph.minDegree = 2 := by sorry

@[category test, AMS 5]
theorem house_max_deg : HouseGraph.maxDegree = 3 := by sorry

@[category test, AMS 5]
theorem house_avg_deg : averageDegree HouseGraph = 12/5 := by sorry

@[category test, AMS 5]
theorem house_matching : m HouseGraph = 2 := by sorry

@[category test, AMS 5]
theorem house_residue : residue HouseGraph = 2 := by sorry

@[category test, AMS 5]
theorem house_annihilation : annihilationNumber HouseGraph = 3 := by sorry

@[category test, AMS 5]
theorem house_cvetkovic : cvetkovic HouseGraph = 3 := by sorry


/-! ### K4 Tests -/

@[category test, AMS 5]
theorem K4_indep : a K4 = 1 := by sorry

@[category test, AMS 5]
theorem K4_dom : dominationNumber K4 = 1 := by sorry

@[category test, AMS 5]
theorem K4_avg_dist : averageDistance K4 = 1 := by sorry

@[category test, AMS 5]
theorem K4_diameter : maxEccentricity K4 = 1 := by sorry

@[category test, AMS 5]
theorem K4_radius : minEccentricity K4 = 1 := by sorry

@[category test, AMS 5]
theorem K4_girth : K4.girth = 3 := by sorry

@[category test, AMS 5]
theorem K4_order : n K4 = 4 := by sorry

@[category test, AMS 5]
theorem K4_size : K4.edgeFinset.card = 6 := by sorry

@[category test, AMS 5]
theorem K4_szeged : szegedIndex K4 = 6 := by sorry

@[category test, AMS 5]
theorem K4_wiener : wienerIndex K4 = 6 := by sorry

@[category test, AMS 5]
theorem K4_min_deg : K4.minDegree = 3 := by sorry

@[category test, AMS 5]
theorem K4_max_deg : K4.maxDegree = 3 := by sorry

@[category test, AMS 5]
theorem K4_avg_deg : averageDegree K4 = 3 := by sorry

@[category test, AMS 5]
theorem K4_matching : m K4 = 2 := by sorry

@[category test, AMS 5]
theorem K4_residue : residue K4 = 1 := by sorry

@[category test, AMS 5]
theorem K4_annihilation : annihilationNumber K4 = 2 := by sorry

@[category test, AMS 5]
theorem K4_cvetkovic : cvetkovic K4 = 1 := by sorry


/-! ### Petersen Graph Tests -/

@[category test, AMS 5]
theorem petersen_indep : a PetersenGraph = 4 := by sorry

@[category test, AMS 5]
theorem petersen_dom : dominationNumber PetersenGraph = 3 := by sorry

@[category test, AMS 5]
theorem petersen_avg_dist : averageDistance PetersenGraph = 5/3 := by sorry

@[category test, AMS 5]
theorem petersen_diameter : maxEccentricity PetersenGraph = 2 := by sorry

@[category test, AMS 5]
theorem petersen_radius : minEccentricity PetersenGraph = 2 := by sorry

@[category test, AMS 5]
theorem petersen_girth : PetersenGraph.girth = 5 := by sorry

@[category test, AMS 5]
theorem petersen_order : n PetersenGraph = 10 := by sorry

@[category test, AMS 5]
theorem petersen_size : PetersenGraph.edgeFinset.card = 15 := by sorry

@[category test, AMS 5]
theorem petersen_szeged : szegedIndex PetersenGraph = 135 := by sorry

@[category test, AMS 5]
theorem petersen_wiener : wienerIndex PetersenGraph = 75 := by sorry

@[category test, AMS 5]
theorem petersen_min_deg : PetersenGraph.minDegree = 3 := by sorry

@[category test, AMS 5]
theorem petersen_max_deg : PetersenGraph.maxDegree = 3 := by sorry

@[category test, AMS 5]
theorem petersen_avg_deg : averageDegree PetersenGraph = 3 := by sorry

@[category test, AMS 5]
theorem petersen_matching : m PetersenGraph = 5 := by sorry

@[category test, AMS 5]
theorem petersen_residue : residue PetersenGraph = 3 := by sorry

@[category test, AMS 5]
theorem petersen_annihilation : annihilationNumber PetersenGraph = 5 := by sorry

@[category test, AMS 5]
theorem petersen_cvetkovic : cvetkovic PetersenGraph = 4 := by sorry


/-! ### C6 Tests -/

@[category test, AMS 5]
theorem C6_indep : a C6 = 3 := by sorry

@[category test, AMS 5]
theorem C6_dom : dominationNumber C6 = 2 := by sorry

@[category test, AMS 5]
theorem C6_avg_dist : averageDistance C6 = 9/5 := by sorry

@[category test, AMS 5]
theorem C6_diameter : maxEccentricity C6 = 3 := by sorry

@[category test, AMS 5]
theorem C6_radius : minEccentricity C6 = 3 := by sorry

@[category test, AMS 5]
theorem C6_girth : C6.girth = 6 := by sorry

@[category test, AMS 5]
theorem C6_order : n C6 = 6 := by sorry

@[category test, AMS 5]
theorem C6_size : C6.edgeFinset.card = 6 := by sorry

@[category test, AMS 5]
theorem C6_szeged : szegedIndex C6 = 54 := by sorry

@[category test, AMS 5]
theorem C6_wiener : wienerIndex C6 = 27 := by sorry

@[category test, AMS 5]
theorem C6_min_deg : C6.minDegree = 2 := by sorry

@[category test, AMS 5]
theorem C6_max_deg : C6.maxDegree = 2 := by sorry

@[category test, AMS 5]
theorem C6_avg_deg : averageDegree C6 = 2 := by sorry

@[category test, AMS 5]
theorem C6_matching : m C6 = 3 := by sorry

@[category test, AMS 5]
theorem C6_residue : residue C6 = 2 := by sorry

@[category test, AMS 5]
theorem C6_annihilation : annihilationNumber C6 = 3 := by sorry

@[category test, AMS 5]
theorem C6_cvetkovic : cvetkovic C6 = 3 := by sorry


/-! ### Star5 Tests -/

@[category test, AMS 5]
theorem Star5_indep : a Star5 = 5 := by sorry

@[category test, AMS 5]
theorem Star5_dom : dominationNumber Star5 = 1 := by sorry

@[category test, AMS 5]
theorem Star5_avg_dist : averageDistance Star5 = 5/3 := by sorry

@[category test, AMS 5]
theorem Star5_diameter : maxEccentricity Star5 = 2 := by sorry

@[category test, AMS 5]
theorem Star5_radius : minEccentricity Star5 = 1 := by sorry

@[category test, AMS 5]
theorem Star5_girth : Star5.egirth = ⊤ := by sorry

@[category test, AMS 5]
theorem Star5_order : n Star5 = 6 := by sorry

@[category test, AMS 5]
theorem Star5_size : Star5.edgeFinset.card = 5 := by sorry

@[category test, AMS 5]
theorem Star5_szeged : szegedIndex Star5 = 25 := by sorry

@[category test, AMS 5]
theorem Star5_wiener : wienerIndex Star5 = 25 := by sorry

@[category test, AMS 5]
theorem Star5_min_deg : Star5.minDegree = 1 := by sorry

@[category test, AMS 5]
theorem Star5_max_deg : Star5.maxDegree = 5 := by sorry

@[category test, AMS 5]
theorem Star5_avg_deg : averageDegree Star5 = 5/3 := by sorry

@[category test, AMS 5]
theorem Star5_matching : m Star5 = 1 := by sorry

@[category test, AMS 5]
theorem Star5_residue : residue Star5 = 5 := by sorry

@[category test, AMS 5]
theorem Star5_annihilation : annihilationNumber Star5 = 5 := by sorry

@[category test, AMS 5]
theorem Star5_cvetkovic : cvetkovic Star5 = 5 := by sorry
