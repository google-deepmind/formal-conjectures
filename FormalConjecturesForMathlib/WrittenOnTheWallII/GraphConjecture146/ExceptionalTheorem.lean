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
public import FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture146.Exceptional

@[expose] public section

/-!
# Completion of the exceptional WOWII 146 case

This file extracts the required metric configuration and applies the explicit
induced-tree constructions from `WrittenOnTheWallII.GraphConjecture146.Proof.Exceptional`.
-/

open Classical
open SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture146.Proof

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- In the sharp radius-one-square, diameter-four, periphery-eccentricity-three
case, the graph contains an induced tree on at least six vertices. -/
theorem exceptional_six_vertex_induced_tree
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hrho : (graphSquare G).radius.toNat = 1)
    (hd : G.diam = 4)
    (hp : eccSet G (maxEccentricityVertices G : Set α) = 3) :
    6 ≤ largestInducedTreeSize G := by
  let B : Set α := maxEccentricityVertices G
  obtain ⟨z, hz⟩ := exists_eccSet_witness_splice (G := G) B
  have hzSet : G.distToSet z B = 3 := by
    calc
      G.distToSet z B = G.eccSet B := hz
      _ = 3 := by simpa [B] using hp
  obtain ⟨x, y, hxyD⟩ := G.exists_dist_eq_diam
  have hxy : G.dist x y = 4 := hxyD.trans hd
  obtain ⟨hxB₀, hyB₀⟩ :=
    diametral_endpoints_mem_maxEccentricityVertices_splice hG hxyD
  have hxB : x ∈ B := by simpa [B] using hxB₀
  have hyB : y ∈ B := by simpa [B] using hyB₀
  have hzNotB : z ∉ B := by
    intro hzB
    have hle : G.distToSet z B ≤ 0 := by
      simpa using distToSet_le_dist_of_mem_public (G := G) z hzB
    omega
  have hfinite : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hG
  have hzxLower : 3 ≤ G.dist z x := by
    calc
      3 = G.distToSet z B := hzSet.symm
      _ ≤ G.dist z x := distToSet_le_dist_of_mem_public (G := G) z hxB
  have hzyLower : 3 ≤ G.dist z y := by
    calc
      3 = G.distToSet z B := hzSet.symm
      _ ≤ G.dist z y := distToSet_le_dist_of_mem_public (G := G) z hyB
  have hzxUpper : G.dist z x ≤ 4 := by
    have h := dist_le_diam (G := G) (u := z) (v := x) hfinite
    simpa [hd] using h
  have hzyUpper : G.dist z y ≤ 4 := by
    have h := dist_le_diam (G := G) (u := z) (v := y) hfinite
    simpa [hd] using h
  have hzxNeFour : G.dist z x ≠ 4 := by
    intro hfour
    have hdiam : G.dist z x = G.diam := hfour.trans hd.symm
    have hzB₀ := (diametral_endpoints_mem_maxEccentricityVertices_splice hG hdiam).1
    exact hzNotB (by simpa [B] using hzB₀)
  have hzyNeFour : G.dist z y ≠ 4 := by
    intro hfour
    have hdiam : G.dist z y = G.diam := hfour.trans hd.symm
    have hzB₀ := (diametral_endpoints_mem_maxEccentricityVertices_splice hG hdiam).1
    exact hzNotB (by simpa [B] using hzB₀)
  have hzx : G.dist z x = 3 := by omega
  have hzy : G.dist z y = 3 := by omega
  have hxz : G.dist x z = 3 := by
    rw [G.dist_comm]
    exact hzx
  obtain ⟨c, hc⟩ := exists_square_center_original_dist_le_two G hG hrho
  have hcxLe : G.dist c x ≤ 2 := hc x
  have hxcLe : G.dist x c ≤ 2 := by
    rw [G.dist_comm]
    exact hcxLe
  have hcyLe : G.dist c y ≤ 2 := hc y
  have hxyTri : G.dist x y ≤ G.dist x c + G.dist c y := hG.dist_triangle
  have hxc : G.dist x c = 2 := by omega
  have hcx : G.dist c x = 2 := by
    rw [G.dist_comm]
    exact hxc
  have hcy : G.dist c y = 2 := by omega
  have hczLe : G.dist c z ≤ 2 := hc z
  have hczNe : c ≠ z := by
    intro h
    subst z
    omega
  have hczPos : 0 < G.dist c z := hG.pos_dist_of_ne hczNe
  have hczCases : G.dist c z = 1 ∨ G.dist c z = 2 := by omega
  obtain ⟨u, hxu, huc⟩ := exists_middle_of_dist_eq_two G hG hxc
  obtain ⟨v, hcv, hvy⟩ := exists_middle_of_dist_eq_two G hG hcy
  rcases hczCases with hczOne | hczTwo
  · have hzc : G.Adj z c := (dist_eq_one_iff_adj.mp hczOne).symm
    have hnzx : ¬G.Adj z x := not_adj_of_two_le_dist G (by omega)
    have hnzy : ¬G.Adj z y := not_adj_of_two_le_dist G (by omega)
    have hnzu : ¬G.Adj z u := by
      intro hzu
      have hle := dist_le_two_of_adj_adj G hzu hxu.symm
      omega
    have hnzv : ¬G.Adj z v := by
      intro hzv
      have hle := dist_le_two_of_adj_adj G hzv hvy
      omega
    have hzxNe : z ≠ x := by
      intro h
      subst x
      simp at hzx
    have hzuNe : z ≠ u := by
      intro h
      subst u
      exact hnzx hxu.symm
    have hzcNe : z ≠ c := hczNe.symm
    have hzvNe : z ≠ v := by
      intro h
      subst v
      exact hnzy hvy
    have hzyNe : z ≠ y := by
      intro h
      subst y
      simp at hzy
    let p : G.Walk x y := .cons hxu (.cons huc (.cons hcv (.cons hvy .nil)))
    have hpGeo : p.length = G.dist x y := by simp [p, hxy]
    have hpFour : p.length = 4 := by simp [p]
    apply WrittenOnTheWallII.GraphConjecture146.Proof.Walk.six_le_largestInducedTreeSize_of_geodesic_four_add_unique_leaf
      p hpGeo hpFour (c := c) (z := z)
    · simp [p]
    · simp [p, hzxNe, hzuNe, hzcNe, hzvNe, hzyNe]
    · exact hzc
    · intro q hq hzq
      simp [p] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · exact (hnzx hzq).elim
      · exact (hnzu hzq).elim
      · rfl
      · exact (hnzv hzq).elim
      · exact (hnzy hzq).elim
  · have hzcTwo : G.dist z c = 2 := by
      rw [G.dist_comm]
      exact hczTwo
    obtain ⟨w, hzw, hwc⟩ := exists_middle_of_dist_eq_two G hG hzcTwo
    by_cases huw : G.Adj u w
    · exact six_le_largestInducedTreeSize_of_cross_arm hG hxy hxz hzy
        hxu huw hzw.symm
    · by_cases hvw : G.Adj v w
      · have hyx : G.dist y x = 4 := by
          rw [G.dist_comm]
          exact hxy
        have hyz : G.dist y z = 3 := by
          rw [G.dist_comm]
          exact hzy
        exact six_le_largestInducedTreeSize_of_cross_arm hG hyx hyz hzx
          hvy.symm hvw hzw.symm
      · have hnwx : ¬G.Adj w x := by
          intro hwx
          have hle := dist_le_two_of_adj_adj G hzw hwx
          omega
        have hnwy : ¬G.Adj w y := by
          intro hwy
          have hle := dist_le_two_of_adj_adj G hzw hwy
          omega
        have hwxNe : w ≠ x := by
          intro h
          subst w
          exact (not_adj_of_two_le_dist G (by omega : 2 ≤ G.dist z x)) hzw
        have hwuNe : w ≠ u := by
          intro h
          subst w
          have hle := dist_le_two_of_adj_adj G hzw hxu.symm
          omega
        have hwcNe : w ≠ c := hwc.ne
        have hwvNe : w ≠ v := by
          intro h
          subst w
          have hle := dist_le_two_of_adj_adj G hzw hvy
          omega
        have hwyNe : w ≠ y := by
          intro h
          subst w
          exact (not_adj_of_two_le_dist G (by omega : 2 ≤ G.dist z y)) hzw
        let p : G.Walk x y := .cons hxu (.cons huc (.cons hcv (.cons hvy .nil)))
        have hpGeo : p.length = G.dist x y := by simp [p, hxy]
        have hpFour : p.length = 4 := by simp [p]
        apply WrittenOnTheWallII.GraphConjecture146.Proof.Walk.six_le_largestInducedTreeSize_of_geodesic_four_add_unique_leaf
          p hpGeo hpFour (c := c) (z := w)
        · simp [p]
        · simp [p, hwxNe, hwuNe, hwcNe, hwvNe, hwyNe]
        · exact hwc
        · intro q hq hwq
          simp [p] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl
          · exact (hnwx hwq).elim
          · exact (huw hwq.symm).elim
          · rfl
          · exact (hvw hwq.symm).elim
          · exact (hnwy hwq).elim

/-- Exact issue-#4 formulation, expressed with the original natural-valued radius. -/
theorem exceptional_case
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hr : G.radius.toNat = 2)
    (hd : G.diam = 4)
    (hp : eccSet G (maxEccentricityVertices G : Set α) = 3) :
    6 ≤ largestInducedTreeSize G := by
  have hrho : (graphSquare G).radius.toNat = 1 := by
    calc
      (graphSquare G).radius.toNat = (G.radius.toNat + 1) / 2 := graphSquare_radius_toNat hG
      _ = 1 := by omega
  exact exceptional_six_vertex_induced_tree G hG hrho hd hp


end WrittenOnTheWallII.GraphConjecture146.Proof
