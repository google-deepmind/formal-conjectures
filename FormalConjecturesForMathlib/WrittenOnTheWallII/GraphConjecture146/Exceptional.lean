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
public import FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture146.Metric

@[expose] public section

/-!
# Exceptional radius-one-square case for WOWII Conjecture 146

The global reduction leaves the sharp case in which the square graph has
radius one, the original diameter is four, and the eccentricity of the
periphery is three. The proof constructs a six-vertex induced tree.
-/

open Classical
open SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture146.Proof

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}

/-- A four-edge geodesic together with a vertex having exactly one neighbor on
that geodesic supplies an induced tree on six vertices. -/
lemma Walk.six_le_largestInducedTreeSize_of_geodesic_four_add_unique_leaf
    {a e z c : α} (p : G.Walk a e)
    (hp : p.length = G.dist a e) (hlen : p.length = 4)
    (hc : c ∈ p.support) (hz : z ∉ p.support)
    (hzc : G.Adj z c)
    (huniq : ∀ ⦃q : α⦄, q ∈ p.support → G.Adj z q → q = c) :
    6 ≤ largestInducedTreeSize G := by
  have hpPath : p.IsPath := p.isPath_of_length_eq_dist hp
  have htree : (G.induce (p.support.toFinset : Set α)).IsTree :=
    p.induce_support_isTree_of_length_eq_dist hp
  have htree' :
      (G.induce ((insert z p.support.toFinset : Finset α) : Set α)).IsTree := by
    apply htree.induce_insert_of_unique_adj
    · simpa using hz
    · simpa using hc
    · exact hzc
    · intro q hq hsq
      exact huniq (by simpa using hq) hsq
  have hcardSupport : p.support.toFinset.card = 5 := by
    rw [List.toFinset_card_of_nodup hpPath.support_nodup, p.length_support, hlen]
  have hcard : (insert z p.support.toFinset).card = 6 := by
    rw [Finset.card_insert_of_notMem (by simpa using hz), hcardSupport]
  have hbound := htree'.card_le_largestInducedTreeSize_splice
  omega

/-- Three successive unique leaf attachments to a three-vertex induced tree
produce an induced tree on six vertices. -/
lemma six_le_largestInducedTreeSize_of_three_unique_insertions
    {s : Finset α} (hT : (G.induce (s : Set α)).IsTree) (hcard : s.card = 3)
    {z₁ a₁ z₂ a₂ z₃ a₃ : α}
    (hz₁ : z₁ ∉ s) (ha₁ : a₁ ∈ s) (hza₁ : G.Adj z₁ a₁)
    (hu₁ : ∀ ⦃q : α⦄, q ∈ s → G.Adj z₁ q → q = a₁)
    (hz₂ : z₂ ∉ insert z₁ s) (ha₂ : a₂ ∈ insert z₁ s) (hza₂ : G.Adj z₂ a₂)
    (hu₂ : ∀ ⦃q : α⦄, q ∈ insert z₁ s → G.Adj z₂ q → q = a₂)
    (hz₃ : z₃ ∉ insert z₂ (insert z₁ s))
    (ha₃ : a₃ ∈ insert z₂ (insert z₁ s)) (hza₃ : G.Adj z₃ a₃)
    (hu₃ : ∀ ⦃q : α⦄, q ∈ insert z₂ (insert z₁ s) → G.Adj z₃ q → q = a₃) :
    6 ≤ largestInducedTreeSize G := by
  have hT₁ := hT.induce_insert_of_unique_adj hz₁ ha₁ hza₁ hu₁
  have hT₂ := hT₁.induce_insert_of_unique_adj hz₂ ha₂ hza₂ hu₂
  have hT₃ := hT₂.induce_insert_of_unique_adj hz₃ ha₃ hza₃ hu₃
  have hcard₁ : (insert z₁ s).card = 4 := by
    rw [Finset.card_insert_of_notMem hz₁, hcard]
  have hcard₂ : (insert z₂ (insert z₁ s)).card = 5 := by
    rw [Finset.card_insert_of_notMem hz₂, hcard₁]
  have hcard₃ : (insert z₃ (insert z₂ (insert z₁ s))).card = 6 := by
    rw [Finset.card_insert_of_notMem hz₃, hcard₂]
  have hbound := hT₃.card_le_largestInducedTreeSize_splice
  omega

/-- The branch in which one of the two length-two diametral arms meets the
length-two `z` arm before the center. No assumption on the other arm is
needed. -/
lemma six_le_largestInducedTreeSize_of_cross_arm
    [Nontrivial α] (hG : G.Connected) {x u w z y : α}
    (hxy : G.dist x y = 4) (hxz : G.dist x z = 3) (hzy : G.dist z y = 3)
    (hxu : G.Adj x u) (huw : G.Adj u w) (hwz : G.Adj w z) :
    6 ≤ largestInducedTreeSize G := by
  have hwzDist : G.dist w z = 1 := dist_eq_one_iff_adj.mpr hwz
  have hxwLe : G.dist x w ≤ 2 := dist_le_two_of_adj_adj G hxu huw
  have hxwLower : 2 ≤ G.dist x w := by
    have htri : G.dist x z ≤ G.dist x w + G.dist w z := hG.dist_triangle
    rw [hxz, hwzDist] at htri
    omega
  have hxw : G.dist x w = 2 := by omega
  have hzx : G.dist z x = 3 := by
    rw [G.dist_comm]
    exact hxz
  have hnzx : ¬G.Adj z x := not_adj_of_two_le_dist G (by omega)
  have hnzy : ¬G.Adj z y := not_adj_of_two_le_dist G (by omega)
  have hnxy : ¬G.Adj x y := not_adj_of_two_le_dist G (by omega)
  have hnzu : ¬G.Adj z u := by
    intro hzu
    have hle := dist_le_two_of_adj_adj G hzu hxu.symm
    omega
  have hnwy : ¬G.Adj w y := by
    intro hwy
    have hle := dist_le_two_of_adj_adj G hwz.symm hwy
    omega
  have hnuy : ¬G.Adj u y := by
    intro huy
    have hle := dist_le_two_of_adj_adj G hxu huy
    omega
  have hzxNe : z ≠ x := by
    intro h
    subst x
    simp at hzx
  have hzuNe : z ≠ u := by
    intro h
    subst u
    exact hnzx hxu.symm
  have hzwNe : z ≠ w := hwz.ne.symm
  have hzyNe : z ≠ y := by
    intro h
    subst y
    simp at hzy
  let p₀ : G.Walk x w := .cons hxu (.cons huw .nil)
  have hp₀ : p₀.length = G.dist x w := by simp [p₀, hxw]
  have hp₀Path : p₀.IsPath := p₀.isPath_of_length_eq_dist hp₀
  have hT₀ : (G.induce (p₀.support.toFinset : Set α)).IsTree :=
    p₀.induce_support_isTree_of_length_eq_dist hp₀
  have hcard₀ : p₀.support.toFinset.card = 3 := by
    rw [List.toFinset_card_of_nodup hp₀Path.support_nodup, p₀.length_support]
    simp [p₀]
  obtain ⟨b, a, hzb, hba, hay⟩ := exists_two_middle_of_dist_eq_three G hG hzy
  have hnza : ¬G.Adj z a := by
    intro hza
    have hle := dist_le_two_of_adj_adj G hza hay
    omega
  have hnaX : ¬G.Adj a x := by
    intro hax
    have hle := dist_le_two_of_adj_adj G hax.symm hay
    omega
  have hnaU : ¬G.Adj a u := by
    intro hau
    have hle := dist_le_three_of_adj_adj_adj G hxu hau.symm hay
    omega
  by_cases hbw : b = w
  · subst b
    let p : G.Walk x y := .cons hxu (.cons huw (.cons hba (.cons hay .nil)))
    have hp : p.length = G.dist x y := by simp [p, hxy]
    have hlen : p.length = 4 := by simp [p]
    have hzaNe : z ≠ a := by
      intro h
      subst a
      exact hnzy hay
    apply WrittenOnTheWallII.GraphConjecture146.Proof.Walk.six_le_largestInducedTreeSize_of_geodesic_four_add_unique_leaf
      p hp hlen (c := w) (z := z)
    · simp [p]
    · simp [p, hzxNe, hzuNe, hzwNe, hzaNe, hzyNe]
    · exact hwz.symm
    · intro q hq hzq
      simp [p] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · exact (hnzx hzq).elim
      · exact (hnzu hzq).elim
      · rfl
      · exact (hnza hzq).elim
      · exact (hnzy hzq).elim
  · have hnbx : ¬G.Adj b x := by
      intro hbx
      have hle := dist_le_two_of_adj_adj G hzb hbx
      omega
    have hbxNe : b ≠ x := by
      intro h
      subst b
      exact hnzx hzb
    have hbuNe : b ≠ u := by
      intro h
      subst b
      exact hnzu hzb
    by_cases hub : G.Adj u b
    · let p : G.Walk x y := .cons hxu (.cons hub (.cons hba (.cons hay .nil)))
      have hp : p.length = G.dist x y := by simp [p, hxy]
      have hlen : p.length = 4 := by simp [p]
      have hzaNe : z ≠ a := by
        intro h
        subst a
        exact hnzy hay
      apply WrittenOnTheWallII.GraphConjecture146.Proof.Walk.six_le_largestInducedTreeSize_of_geodesic_four_add_unique_leaf
        p hp hlen (c := b) (z := z)
      · simp [p]
      · simp [p, hzxNe, hzuNe, hzb.ne, hzaNe, hzyNe]
      · exact hzb
      · intro q hq hzq
        simp [p] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl
        · exact (hnzx hzq).elim
        · exact (hnzu hzq).elim
        · rfl
        · exact (hnza hzq).elim
        · exact (hnzy hzq).elim
    · by_cases hwa : G.Adj w a
      · let p : G.Walk x y := .cons hxu (.cons huw (.cons hwa (.cons hay .nil)))
        have hp : p.length = G.dist x y := by simp [p, hxy]
        have hlen : p.length = 4 := by simp [p]
        have hzaNe : z ≠ a := by
          intro h
          subst a
          exact hnzy hay
        apply WrittenOnTheWallII.GraphConjecture146.Proof.Walk.six_le_largestInducedTreeSize_of_geodesic_four_add_unique_leaf
          p hp hlen (c := w) (z := z)
        · simp [p]
        · simp [p, hzxNe, hzuNe, hzwNe, hzaNe, hzyNe]
        · exact hwz.symm
        · intro q hq hzq
          simp [p] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl
          · exact (hnzx hzq).elim
          · exact (hnzu hzq).elim
          · rfl
          · exact (hnza hzq).elim
          · exact (hnzy hzq).elim
      · by_cases hwb : G.Adj w b
        · have hbaNe : a ≠ b := hba.ne.symm
          have haxNe : a ≠ x := by
            intro h
            subst a
            exact hnxy hay
          have hauNe : a ≠ u := by
            intro h
            subst a
            exact hnuy hay
          have hawNe : a ≠ w := by
            intro h
            subst a
            exact hnwy hay
          have hyxNe : y ≠ x := by
            intro h
            subst y
            simp at hxy
          have hyuNe : y ≠ u := by
            intro h
            subst y
            exact hnxy hxu
          have hywNe : y ≠ w := by
            intro h
            subst y
            exact hnzy hwz.symm
          have hybNe : y ≠ b := by
            intro h
            subst y
            exact hnzy hzb
          have hyaNe : y ≠ a := hay.ne.symm
          have hnyb : ¬G.Adj y b := by
            intro hyb
            have hle := dist_le_two_of_adj_adj G hzb hyb.symm
            omega
          apply six_le_largestInducedTreeSize_of_three_unique_insertions hT₀ hcard₀
            (z₁ := b) (a₁ := w) (z₂ := a) (a₂ := b) (z₃ := y) (a₃ := a)
          · simp [p₀, hbxNe, hbuNe, hbw]
          · simp [p₀]
          · exact hwb.symm
          · intro q hq hbq
            simp [p₀] at hq
            rcases hq with rfl | rfl | rfl
            · exact (hnbx hbq).elim
            · exact (hub hbq.symm).elim
            · rfl
          · simp [p₀, hbaNe, haxNe, hauNe, hawNe]
          · simp
          · exact hba.symm
          · intro q hq haq
            simp [p₀] at hq
            rcases hq with rfl | rfl | rfl | rfl
            · rfl
            · exact (hnaX haq).elim
            · exact (hnaU haq).elim
            · exact (hwa haq.symm).elim
          · simp [p₀, hyxNe, hyuNe, hywNe, hybNe, hyaNe]
          · simp
          · exact hay.symm
          · intro q hq hyq
            simp [p₀] at hq
            rcases hq with rfl | rfl | rfl | rfl | rfl
            · rfl
            · exact (hnyb hyq).elim
            · exact (hnxy hyq.symm).elim
            · exact (hnuy hyq.symm).elim
            · exact (hnwy hyq.symm).elim
        · have hbzNe : b ≠ z := hzb.ne.symm
          have hbaNe : a ≠ b := hba.ne.symm
          have hazNe : a ≠ z := by
            intro h
            subst a
            exact hnzy hay
          have haxNe : a ≠ x := by
            intro h
            subst a
            exact hnxy hay
          have hauNe : a ≠ u := by
            intro h
            subst a
            exact hnuy hay
          have hawNe : a ≠ w := by
            intro h
            subst a
            exact hnwy hay
          apply six_le_largestInducedTreeSize_of_three_unique_insertions hT₀ hcard₀
            (z₁ := z) (a₁ := w) (z₂ := b) (a₂ := z) (z₃ := a) (a₃ := b)
          · simp [p₀, hzxNe, hzuNe, hzwNe]
          · simp [p₀]
          · exact hwz.symm
          · intro q hq hzq
            simp [p₀] at hq
            rcases hq with rfl | rfl | rfl
            · exact (hnzx hzq).elim
            · exact (hnzu hzq).elim
            · rfl
          · simp [p₀, hbzNe, hbxNe, hbuNe, hbw]
          · simp
          · exact hzb.symm
          · intro q hq hbq
            simp [p₀] at hq
            rcases hq with rfl | rfl | rfl | rfl
            · rfl
            · exact (hnbx hbq).elim
            · exact (hub hbq.symm).elim
            · exact (hwb hbq.symm).elim
          · simp [p₀, hbaNe, hazNe, haxNe, hauNe, hawNe]
          · simp
          · exact hba.symm
          · intro q hq haq
            simp [p₀] at hq
            rcases hq with rfl | rfl | rfl | rfl | rfl
            · rfl
            · exact (hnza haq.symm).elim
            · exact (hnaX haq).elim
            · exact (hnaU haq).elim
            · exact (hwa haq.symm).elim

end WrittenOnTheWallII.GraphConjecture146.Proof
