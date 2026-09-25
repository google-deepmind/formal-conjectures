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
# Erdős Problem 62

*References:*
- [erdosproblems.com/62](https://www.erdosproblems.com/62)
- [Er87] Erdős, Paul, *Some problems on finite and infinite graphs*. Logic and combinatorics
  (Arcata, Calif., 1985), Contemp. Math. 65 (1987), 223-228.
- [Er90] Erdős, Paul, *Some of my favourite unsolved problems*. A tribute to Paul Erdős (1990),
  467-478.
- [Er95d] Erdős, Paul, *Some of my favourite problems in various branches of combinatorics*.
  Matematiche (Catania) 47 (1992), no. 2, 231-240 (1995).
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference "Paul
  Erdős and his mathematics", Budapest, July 1999 (1999), Problem 7.89.
-/

@[expose] public section

open Cardinal SimpleGraph

namespace Erdos62

/--
If $G_1, G_2$ are two graphs with chromatic number $\aleph_1$, must there exist a graph $G$
with chromatic number $4$ which is a subgraph of both $G_1$ and $G_2$?

"Subgraph" means a copy up to isomorphism, expressed by `SimpleGraph.IsContained` (`⊑`).
-/
@[category research open, AMS 3 5]
theorem erdos_62 :
    answer(sorry) ↔
      ∀ (V₁ V₂ : Type) (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
        G₁.chromaticCardinal = ℵ_ 1 → G₂.chromaticCardinal = ℵ_ 1 →
          ∃ (W : Type) (G : SimpleGraph W), G.chromaticCardinal = 4 ∧ G ⊑ G₁ ∧ G ⊑ G₂ := by
  sorry

/--
The stronger version: if $G_1, G_2$ are two graphs with chromatic number $\aleph_1$, must
there exist a graph $G$ with chromatic number $\aleph_0$ which is a subgraph of both
$G_1$ and $G_2$?
-/
@[category research open, AMS 3 5]
theorem erdos_62.variants.aleph0 :
    answer(sorry) ↔
      ∀ (V₁ V₂ : Type) (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
        G₁.chromaticCardinal = ℵ_ 1 → G₂.chromaticCardinal = ℵ_ 1 →
          ∃ (W : Type) (G : SimpleGraph W), G.chromaticCardinal = ℵ₀ ∧ G ⊑ G₁ ∧ G ⊑ G₂ := by
  sorry

/--
Erdős also asked [Er87]: given finitely many graphs $G_1, \dots, G_n$ with chromatic number
$\aleph_1$, must there be a graph $H$ with chromatic number $4$ or $\aleph_0$ which is a
subgraph of every $G_i$?
-/
@[category research open, AMS 3 5]
theorem erdos_62.variants.finite_collection :
    answer(sorry) ↔
      ∀ (n : ℕ) (V : Fin n → Type) (G : ∀ i, SimpleGraph (V i)),
        (∀ i, (G i).chromaticCardinal = ℵ_ 1) →
          ∃ (W : Type) (H : SimpleGraph W),
            (H.chromaticCardinal = 4 ∨ H.chromaticCardinal = ℵ₀) ∧ ∀ i, H ⊑ G i := by
  sorry

/--
Erdős wrote [Er87] that 'probably' every graph with chromatic number $\aleph_1$ contains as
subgraphs all graphs with chromatic number $4$ with sufficiently large girth.

We state this for finite graphs $H$. The girth bound $g$ may depend on $G$. Since there are
finite graphs with chromatic number $4$ and arbitrarily large girth, a positive answer implies
a positive answer to `erdos_62`.
-/
@[category research open, AMS 3 5]
theorem erdos_62.variants.large_girth :
    answer(sorry) ↔
      ∀ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = ℵ_ 1 →
        ∃ g : ℕ, ∀ (W : Type) [Finite W] (H : SimpleGraph W),
          H.chromaticCardinal = 4 → g ≤ H.girth → H ⊑ G := by
  sorry

/-! ## Relations between the variants -/

@[category API, AMS 5]
theorem chromaticCardinal_le_of_colorable {V : Type} (G : SimpleGraph V) {n : ℕ}
    (h : G.Colorable n) : G.chromaticCardinal ≤ n := by
  obtain ⟨c⟩ := h
  apply csInf_le (OrderBot.bddBelow _)
  exact ⟨Fin n, by simp, ⟨c⟩⟩

@[category API, AMS 5]
theorem colorable_of_chromaticCardinal_lt {V : Type} (G : SimpleGraph V) {n : ℕ}
    (h : G.chromaticCardinal < (n + 1 : ℕ)) : G.Colorable n := by
  have hne : {κ : Cardinal | ∃ (C : Type) (_ : #C = κ), Nonempty (G.Coloring C)}.Nonempty :=
    ⟨#V, V, rfl, ⟨Coloring.mk id fun h => G.ne_of_adj h⟩⟩
  obtain ⟨α, hα, ⟨c⟩⟩ := csInf_mem hne
  have hlt : #α < (n + 1 : ℕ) := by
    rw [hα]
    exact h
  rw [Nat.cast_succ, ← Cardinal.succ_natCast, Order.lt_succ_iff] at hlt
  have : #α ≤ #(Fin n) := by simpa using hlt
  obtain ⟨e⟩ := this
  exact ⟨(Embedding.completeGraph e).toHom.comp c⟩

@[category API, AMS 5]
theorem chromaticCardinal_eq_natCast {V : Type} (G : SimpleGraph V) (n : ℕ)
    (h₁ : G.Colorable (n + 1)) (h₂ : ¬ G.Colorable n) :
    G.chromaticCardinal = (n + 1 : ℕ) :=
  le_antisymm (chromaticCardinal_le_of_colorable G h₁)
    (not_lt.1 fun h => h₂ (colorable_of_chromaticCardinal_lt G h))

/-- A graph which is not `3`-colourable contains a finite induced subgraph of chromatic
number `4`. -/
@[category API, AMS 5]
theorem exists_isContained_chromaticCardinal_eq_four {V : Type} (G : SimpleGraph V)
    (hG : ¬ G.Colorable 3) :
    ∃ (W : Type) (H : SimpleGraph W), H.chromaticCardinal = 4 ∧ H ⊑ G := by
  -- By compactness, some finite induced subgraph is not `3`-colourable.
  have hex : ∃ n, ∃ S : Set V, S.Finite ∧ S.ncard = n ∧ ¬ (G.induce S).Colorable 3 := by
    by_contra hcon
    push Not at hcon
    apply hG
    obtain ⟨f⟩ := nonempty_hom_of_forall_finite_subgraph_hom
      (F := (⊤ : SimpleGraph (Fin 3))) (G := G) fun G' hG' =>
        (hcon _ G'.verts hG' rfl).some.comp ⟨id, fun h => G'.adj_sub h⟩
    exact ⟨f⟩
  classical
  obtain ⟨S, hSfin, hScard, hSnot⟩ := Nat.find_spec hex
  have hmin : ∀ T : Set V, T.Finite → T.ncard < Nat.find hex → (G.induce T).Colorable 3 :=
    fun T hT hlt => by
      by_contra hc
      exact Nat.find_min hex hlt ⟨T, hT, rfl, hc⟩
  have hSne : S.Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty] at he
    subst he
    exact hSnot ⟨Coloring.mk (fun w => absurd w.2 (Set.notMem_empty _))
      fun {a} _ => absurd a.2 (Set.notMem_empty _)⟩
  obtain ⟨v, hv⟩ := hSne
  obtain ⟨c⟩ := hmin (S \ {v}) hSfin.sdiff (by
    rw [← hScard]
    exact Set.ncard_sdiff_singleton_lt_of_mem hv hSfin)
  have h4 : (G.induce S).Colorable 4 := by
    refine ⟨Coloring.mk
      (fun w => if h : (w : V) = v then 3 else (c ⟨w, w.2, h⟩).castSucc) ?_⟩
    intro a b hab
    by_cases ha : (a : V) = v <;> by_cases hb : (b : V) = v
    · exact absurd (ha.trans hb.symm) (G.ne_of_adj hab)
    · simp only [ha, hb, dite_true, dite_false]
      exact (Fin.castSucc_lt_last _).ne'
    · simp only [ha, hb, dite_true, dite_false]
      exact (Fin.castSucc_lt_last _).ne
    · simp only [ha, hb, dite_false]
      intro heq
      exact c.valid (show (G.induce (S \ {v})).Adj ⟨a, a.2, ha⟩ ⟨b, b.2, hb⟩ from hab)
        (Fin.castSucc_injective _ heq)
  refine ⟨S, G.induce S, ?_, ⟨⟨(Embedding.induce (G := G) S).toHom,
    (Embedding.induce (G := G) S).injective⟩⟩⟩
  rw [chromaticCardinal_eq_natCast (G.induce S) 3 h4 hSnot]
  norm_num

@[category API, AMS 5]
theorem not_colorable_three_of_chromaticCardinal_eq_aleph0 {V : Type} {G : SimpleGraph V}
    (h : G.chromaticCardinal = ℵ₀) : ¬ G.Colorable 3 := fun hc => by
  have := chromaticCardinal_le_of_colorable G hc
  rw [h] at this
  exact absurd this (not_le.2 (Cardinal.natCast_lt_aleph0 (n := 3)))

/-- A positive answer to `erdos_62.variants.aleph0` gives a positive answer to `erdos_62`. -/
@[category API, AMS 5]
theorem erdos_62_of_aleph0
    (h : ∀ (V₁ V₂ : Type) (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
      G₁.chromaticCardinal = ℵ_ 1 → G₂.chromaticCardinal = ℵ_ 1 →
        ∃ (W : Type) (G : SimpleGraph W), G.chromaticCardinal = ℵ₀ ∧ G ⊑ G₁ ∧ G ⊑ G₂) :
    ∀ (V₁ V₂ : Type) (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
      G₁.chromaticCardinal = ℵ_ 1 → G₂.chromaticCardinal = ℵ_ 1 →
        ∃ (W : Type) (G : SimpleGraph W), G.chromaticCardinal = 4 ∧ G ⊑ G₁ ∧ G ⊑ G₂ := by
  intro V₁ V₂ G₁ G₂ h₁ h₂
  obtain ⟨W, H, hH, hs₁, hs₂⟩ := h V₁ V₂ G₁ G₂ h₁ h₂
  obtain ⟨W', H', hH', hs⟩ := exists_isContained_chromaticCardinal_eq_four H
    (not_colorable_three_of_chromaticCardinal_eq_aleph0 hH)
  exact ⟨W', H', hH', hs.trans hs₁, hs.trans hs₂⟩

/-- The graphs `G₁, G₂` as a `Fin 2`-indexed family. -/
def pairFamily {V₁ V₂ : Type} (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) :
    ∀ i : Fin 2, SimpleGraph (![V₁, V₂] i) :=
  fun i => Fin.cases (motive := fun i => SimpleGraph (![V₁, V₂] i)) G₁
    (fun j => Fin.cases (motive := fun j => SimpleGraph (![V₁, V₂] j.succ)) G₂
      (fun k => k.elim0) j) i

/-- A positive answer to `erdos_62.variants.finite_collection` gives a positive answer to
`erdos_62`. -/
@[category API, AMS 5]
theorem erdos_62_of_finite_collection
    (h : ∀ (n : ℕ) (V : Fin n → Type) (G : ∀ i, SimpleGraph (V i)),
      (∀ i, (G i).chromaticCardinal = ℵ_ 1) →
        ∃ (W : Type) (H : SimpleGraph W),
          (H.chromaticCardinal = 4 ∨ H.chromaticCardinal = ℵ₀) ∧ ∀ i, H ⊑ G i) :
    ∀ (V₁ V₂ : Type) (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
      G₁.chromaticCardinal = ℵ_ 1 → G₂.chromaticCardinal = ℵ_ 1 →
        ∃ (W : Type) (G : SimpleGraph W), G.chromaticCardinal = 4 ∧ G ⊑ G₁ ∧ G ⊑ G₂ := by
  intro V₁ V₂ G₁ G₂ h₁ h₂
  obtain ⟨W, H, hH, hs⟩ := h 2 ![V₁, V₂] (pairFamily G₁ G₂) fun i => by
    fin_cases i
    exacts [h₁, h₂]
  rcases hH with hH | hH
  · exact ⟨W, H, hH, hs 0, hs 1⟩
  · obtain ⟨W', H', hH', hs'⟩ := exists_isContained_chromaticCardinal_eq_four H
      (not_colorable_three_of_chromaticCardinal_eq_aleph0 hH)
    exact ⟨W', H', hH', hs'.trans (hs 0), hs'.trans (hs 1)⟩

end Erdos62
