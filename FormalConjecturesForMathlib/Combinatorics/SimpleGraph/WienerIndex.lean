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

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance

@[expose] public section

namespace SimpleGraph
open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The Wiener index of `G`, which is the sum of distances between all
pairs of vertices. -/
noncomputable def wienerIndex (G : SimpleGraph α) : ℕ :=
  ∑ uv : Sym2 α, uv.lift ⟨fun u v ↦ G.dist u v, by simp [dist_comm]⟩

/-- Computable Wiener index: half the sum of all ordered pairwise distances. -/
def computable_wiener (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (∑ u ∈ Finset.univ, ∑ v ∈ Finset.univ, computable_dist G u v) / 2


-- Helper: ∑∑ f = 2 * ∑ Sym2 (lift f) when f symmetric with f(a,a) = 0
private lemma double_sum_eq_two_mul_sym2_sum {f : α → α → ℕ}
    (hf : ∀ a b, f a b = f b a) (hd : ∀ a, f a a = 0) :
    ∑ u : α, ∑ v : α, f u v =
    2 * ∑ x : Sym2 α, Sym2.lift ⟨f, fun a b => hf a b⟩ x := by
  -- Use fiberwise decomposition over Sym2 quotient map
  have h_fiber := Fintype.sum_fiberwise
    (fun (p : α × α) => s(p.1, p.2))
    (fun (p : α × α) => f p.1 p.2)
  -- h_fiber : ∑ q : Sym2 α, ∑ p : {p // Sym2.mk p = q}, f (↑p).1 (↑p).2
  --         = ∑ p : α × α, f p.1 p.2
  -- RHS = ∑ u, ∑ v, f u v (by Finset.sum_product')
  -- LHS = ∑ q, (fiber sum) = ∑ q, 2 * lift f q = 2 * ∑ q, lift f q
  -- So: ∑ u, ∑ v, f u v = 2 * ∑ q, lift f q
  rw [show (∑ u : α, ∑ v : α, f u v) = ∑ p : α × α, f p.1 p.2 from by
    rw [← Finset.univ_product_univ, Finset.sum_product']]
  rw [← h_fiber, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  -- For each q : Sym2 α, show fiber sum = 2 * lift f q
  refine Sym2.ind (fun a b => ?_) q
  simp only [Sym2.lift_mk]
  -- Need: ∑ (p : {p : α × α // Sym2.mk p = s(a, b)}), f (↑p).1 (↑p).2 = 2 * f a b
  -- Convert subtype sum to filter sum
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : α × α => s(p.1, p.2) = s(a, b)))
    (fun x => by simp [Finset.mem_filter]) (fun p => f p.1 p.2)]
  -- Characterize the filter: Sym2.mk (x,y) = s(a,b) ↔ (x,y) = (a,b) ∨ (x,y) = (b,a)
  have h_filter : Finset.univ.filter (fun p : α × α => s(p.1, p.2) = s(a, b)) =
      {(a, b), (b, a)} := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · intro h
      rw [Sym2.eq] at h
      cases h with
      | refl => left; exact ⟨rfl, rfl⟩
      | swap => right; exact ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · rfl
      · exact Sym2.sound (.swap _ _)
  rw [h_filter]
  by_cases hab : a = b
  · subst hab; simp [hd]
  · rw [Finset.sum_pair (show (a, b) ≠ (b, a) by simp [hab])]
    rw [hf b a]; ring


theorem wiener_eq_computable (G : SimpleGraph α) [DecidableRel G.Adj] :
    wienerIndex G = computable_wiener G := by
  unfold wienerIndex computable_wiener
  -- Goal: ∑ uv, Sym2.lift ⟨dist, _⟩ uv = (∑ u, ∑ v, computable_dist u v) / 2
  have hcomm : ∀ a b, computable_dist G a b = computable_dist G b a := by
    intro a b; rw [← dist_eq_computable, ← dist_eq_computable, dist_comm]
  have hdiag : ∀ a, computable_dist G a a = 0 := by
    intro a; rw [← dist_eq_computable]; simp
  -- Sum over Sym2 using dist = sum over Sym2 using computable_dist
  have h_sum : (∑ uv : Sym2 α, Sym2.lift ⟨fun u v ↦ G.dist u v,
      by intro a b; simp [dist_comm]⟩ uv) =
      ∑ uv : Sym2 α, Sym2.lift ⟨fun u v ↦ computable_dist G u v,
      fun a b => hcomm a b⟩ uv := by
    apply Finset.sum_congr rfl; intro x _
    refine Sym2.ind (fun a b => ?_) x
    simp only [Sym2.lift_mk, dist_eq_computable]
  rw [h_sum]
  have h2 := double_sum_eq_two_mul_sym2_sum hcomm hdiag
  -- h2 : ∑∑ f = 2 * ∑ Sym2 lift f
  -- goal: ∑ Sym2 lift f = ∑∑ f / 2
  rw [h2, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
end SimpleGraph
