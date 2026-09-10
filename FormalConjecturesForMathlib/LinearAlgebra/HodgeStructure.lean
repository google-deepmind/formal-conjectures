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

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# Rational Hodge structures

This file defines a pure rational Hodge structure on a rational vector space. Its complexification
is the actual scalar extension `ℂ ⊗[ℚ] V`. Complex conjugation acts on the first tensor
factor, so the rational lattice and the conjugation symmetry are not additional data.

The Hodge pieces are the only data in a `PureHodgeStructure`. They must form a direct-sum
decomposition, vanish off the prescribed weight, and be exchanged by the constructed conjugation.
Hodge classes are then a derived preimage of the middle piece.
-/

@[expose] public noncomputable section

open scoped DirectSum TensorProduct

universe u

namespace HodgeStructure

/-- The canonical map from a `K`-vector space to its complexification. -/
def ofBase (K : Type) [Field K] [Algebra K ℂ] (V : Type u) [AddCommGroup V] [Module K V] :
    V →ₗ[K] ℂ ⊗[K] V :=
  TensorProduct.mk K ℂ V 1

@[simp]
lemma ofBase_apply (K : Type) [Field K] [Algebra K ℂ] (V : Type u) [AddCommGroup V] [Module K V]
    (v : V) : ofBase K V v = 1 ⊗ₜ[K] v := rfl

variable (V : Type u) [AddCommGroup V] [Module ℚ V]

/-- Complex conjugation on a complexified rational vector space. It conjugates the scalar factor
and fixes every rational vector. -/
def conjugate : ℂ ⊗[ℚ] V →ₗ[ℚ] ℂ ⊗[ℚ] V :=
  TensorProduct.map (Complex.conjAe.restrictScalars ℚ).toLinearMap LinearMap.id

@[simp]
lemma conjugate_tmul (z : ℂ) (v : V) :
    conjugate V (z ⊗ₜ[ℚ] v) = Complex.conjAe z ⊗ₜ[ℚ] v := rfl

@[simp]
lemma conjugate_ofBase (v : V) : conjugate V (ofBase ℚ V v) = ofBase ℚ V v := by
  simp

@[simp]
lemma conjugate_conjugate (x : ℂ ⊗[ℚ] V) : conjugate V (conjugate V x) = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro z v
    simp
  · intro x y hx hy
    simp [hx, hy]

/-- A pure rational Hodge structure of weight `n` on `V`.

The pieces are indexed by pairs `(p,q)`. They form an internal direct sum, only pieces with
`p + q = n` can be nonzero, and complex conjugation exchanges the `(p,q)` and `(q,p)` pieces. -/
structure Pure (n : ℕ) where
  /-- The Hodge piece `V^{p,q}` inside `V_ℂ`. -/
  piece : ℕ → ℕ → Submodule ℂ (ℂ ⊗[ℚ] V)
  /-- Hodge pieces off the prescribed weight are zero. -/
  piece_eq_bot_of_add_ne : ∀ p q, p + q ≠ n → piece p q = ⊥
  /-- Every complexified vector has a unique finite decomposition into Hodge pieces. -/
  isInternal : DirectSum.IsInternal (fun pq : ℕ × ℕ ↦ piece pq.1 pq.2)
  /-- The constructed complex conjugation exchanges bidegrees. -/
  conjugate_mem_iff : ∀ p q x, conjugate V x ∈ piece p q ↔ x ∈ piece q p

namespace Pure

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {n : ℕ}

/-- The Hodge pieces span the whole complexification. -/
lemma iSup_piece_eq_top (H : Pure V n) :
    ⨆ pq : ℕ × ℕ, H.piece pq.1 pq.2 = ⊤ :=
  H.isInternal.submodule_iSup_eq_top

/-- Membership in a conjugate Hodge piece, with conjugation moved to the other side. -/
lemma mem_piece_conjugate_iff (H : Pure V n) (p q : ℕ) (x : ℂ ⊗[ℚ] V) :
    x ∈ H.piece p q ↔ conjugate V x ∈ H.piece q p :=
  (H.conjugate_mem_iff q p x).symm

/-- The Hodge filtration `F^p V_ℂ`, constructed as the sum of pieces whose first index is at
least `p`. -/
def filtration (H : Pure V n) (p : ℕ) : Submodule ℂ (ℂ ⊗[ℚ] V) :=
  ⨆ a : ℕ, ⨆ (_ : p ≤ a), ⨆ b : ℕ, H.piece a b

/-- A piece with first index at least `p` lies in `F^p`. -/
lemma piece_le_filtration (H : Pure V n) {p a b : ℕ} (ha : p ≤ a) :
    H.piece a b ≤ H.filtration p :=
  le_iSup_of_le a <| le_iSup_of_le ha <| le_iSup (fun b' ↦ H.piece a b') b

/-- Rational Hodge classes of codimension `p`: rational vectors whose complexifications lie in
the middle Hodge piece `V^{p,p}`. -/
def hodgeClasses (p : ℕ) (H : Pure V (2 * p)) : Submodule ℚ V :=
  Submodule.comap (ofBase ℚ V) ((H.piece p p).restrictScalars ℚ)

/-- The defining membership criterion for a rational Hodge class. -/
lemma mem_hodgeClasses_iff (p : ℕ) (H : Pure V (2 * p)) (x : V) :
    x ∈ hodgeClasses p H ↔ ofBase ℚ V x ∈ H.piece p p :=
  Iff.rfl

/-- Every rational Hodge class lies in the corresponding Hodge filtration after
complexification. -/
lemma ofBase_mem_filtration {p : ℕ} (H : Pure V (2 * p))
    {x : V} (hx : x ∈ hodgeClasses p H) :
    ofBase ℚ V x ∈ H.filtration p :=
  H.piece_le_filtration le_rfl hx

/-- The direct-sum coordinates of a pure Hodge structure. -/
noncomputable def decomposition (H : Pure V n) :
    ℂ ⊗[ℚ] V ≃ₗ[ℂ] (⨁ pq : ℕ × ℕ, H.piece pq.1 pq.2) :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun pq : ℕ × ℕ ↦ H.piece pq.1 pq.2)
    H.isInternal).symm

/-- A vector in one Hodge piece has only that direct-sum coordinate. -/
lemma decomposition_apply_of_mem (H : Pure V n) {pq : ℕ × ℕ}
    {x : ℂ ⊗[ℚ] V} (hx : x ∈ H.piece pq.1 pq.2) :
    H.decomposition x =
      DirectSum.lof ℂ (ℕ × ℕ) (fun ab ↦ H.piece ab.1 ab.2) pq ⟨x, hx⟩ :=
  H.decomposition.symm.injective (by
    rw [LinearEquiv.symm_apply_apply]
    change x = DirectSum.coeLinearMap (fun ab : ℕ × ℕ ↦ H.piece ab.1 ab.2)
      (DirectSum.lof ℂ (ℕ × ℕ) (fun ab ↦ H.piece ab.1 ab.2) pq ⟨x, hx⟩)
    simp)

/-- Sum of the Hodge pieces indexed by a set of bidegrees. -/
noncomputable def pieceSum (H : Pure V n) (s : Set (ℕ × ℕ)) :
    Submodule ℂ (ℂ ⊗[ℚ] V) :=
  ⨆ pq, ⨆ (_ : pq ∈ s), H.piece pq.1 pq.2

lemma pieceSum_mono (H : Pure V n) {s t : Set (ℕ × ℕ)} (hst : s ⊆ t) :
    H.pieceSum s ≤ H.pieceSum t :=
  iSup₂_le fun pq hpq ↦ le_iSup₂_of_le pq (hst hpq) le_rfl

lemma piece_le_pieceSum (H : Pure V n) {s : Set (ℕ × ℕ)} {pq : ℕ × ℕ}
    (hpq : pq ∈ s) : H.piece pq.1 pq.2 ≤ H.pieceSum s :=
  le_iSup₂_of_le pq hpq le_rfl

lemma pieceSum_union (H : Pure V n) (s t : Set (ℕ × ℕ)) :
    H.pieceSum (s ∪ t) = H.pieceSum s ⊔ H.pieceSum t := by
  apply le_antisymm
  · exact iSup₂_le fun pq hpq ↦ hpq.elim
      (fun hs ↦ (H.piece_le_pieceSum hs).trans le_sup_left)
      (fun ht ↦ (H.piece_le_pieceSum ht).trans le_sup_right)
  · exact sup_le (H.pieceSum_mono Set.subset_union_left)
      (H.pieceSum_mono Set.subset_union_right)

lemma pieceSum_singleton (H : Pure V n) (pq : ℕ × ℕ) :
    H.pieceSum {pq} = H.piece pq.1 pq.2 := by
  apply le_antisymm
  · exact iSup₂_le fun ab hab ↦ le_of_eq (by rw [show ab = pq from hab])
  · exact H.piece_le_pieceSum (Set.mem_singleton pq)

lemma disjoint_pieceSum (H : Pure V n) {s t : Set (ℕ × ℕ)}
    (hst : Disjoint s t) : Disjoint (H.pieceSum s) (H.pieceSum t) :=
  H.isInternal.submodule_iSupIndep.disjoint_biSup_biSup hst

lemma filtration_eq_pieceSum (H : Pure V n) (p : ℕ) :
    H.filtration p = H.pieceSum {pq | p ≤ pq.1} := by
  apply le_antisymm
  · exact iSup_le fun a ↦ iSup_le fun ha ↦ iSup_le fun b ↦
      H.piece_le_pieceSum (s := {pq | p ≤ pq.1}) (pq := (a, b)) ha
  · exact iSup₂_le fun pq hpq ↦
      le_iSup_of_le pq.1 <| le_iSup_of_le hpq <| le_iSup (fun b ↦ H.piece pq.1 b) pq.2

/-- The conjugate filtration, written as the sum of pieces whose second index is large. -/
noncomputable def conjugateFiltration (H : Pure V n) (p : ℕ) :
    Submodule ℂ (ℂ ⊗[ℚ] V) := H.pieceSum {pq | p ≤ pq.2}

lemma conjugate_mem_filtration (H : Pure V n) (p : ℕ) {x : ℂ ⊗[ℚ] V}
    (hx : x ∈ H.filtration p) : conjugate V x ∈ H.conjugateFiltration p := by
  rw [H.filtration_eq_pieceSum] at hx
  induction hx using Submodule.iSup_induction' with
  | mem pq x hx =>
      induction hx using Submodule.iSup_induction' with
      | mem hpq x hx =>
          exact H.piece_le_pieceSum
              (s := {ab : ℕ × ℕ | p ≤ ab.2}) (pq := (pq.2, pq.1)) hpq <|
            (H.conjugate_mem_iff pq.2 pq.1 x).2 hx
      | zero => simp
      | add x y _ _ hx hy => simpa using (H.conjugateFiltration p).add_mem hx hy
  | zero => simp
  | add x y _ _ hx hy => simpa using (H.conjugateFiltration p).add_mem hx hy

private def firstLarge (p : ℕ) : Set (ℕ × ℕ) := {pq | p ≤ pq.1}
private def secondLarge (p : ℕ) : Set (ℕ × ℕ) := {pq | p ≤ pq.2}
private def firstOnly (p : ℕ) : Set (ℕ × ℕ) := firstLarge p \ secondLarge p
private def secondOnly (p : ℕ) : Set (ℕ × ℕ) := secondLarge p \ firstLarge p

private lemma pieceSum_firstLarge (p : ℕ) (H : Pure V (2 * p)) :
    H.pieceSum (firstLarge p) =
      H.piece p p ⊔ H.pieceSum (firstOnly p) := by
  apply le_antisymm
  · refine iSup₂_le fun pq hpq ↦ ?_
    by_cases hsecond : pq ∈ secondLarge p
    · by_cases hpp : pq = (p, p)
      · subst pq
        exact le_sup_left
      · have hadd : pq.1 + pq.2 ≠ 2 * p := by
          intro heq
          have h1 : p ≤ pq.1 := hpq
          have h2 : p ≤ pq.2 := hsecond
          have h : pq.1 = p ∧ pq.2 = p := by lia
          exact hpp (Prod.ext h.1 h.2)
        rw [H.piece_eq_bot_of_add_ne pq.1 pq.2 hadd]
        exact bot_le
    · exact (H.piece_le_pieceSum (s := firstOnly p) (pq := pq)
        ⟨hpq, hsecond⟩).trans le_sup_right
  · refine sup_le ?_ (H.pieceSum_mono Set.sdiff_subset)
    exact H.piece_le_pieceSum (show (p, p) ∈ firstLarge p by simp [firstLarge])

private lemma pieceSum_secondLarge (p : ℕ) (H : Pure V (2 * p)) :
    H.pieceSum (secondLarge p) =
      H.piece p p ⊔ H.pieceSum (secondOnly p) := by
  apply le_antisymm
  · refine iSup₂_le fun pq hpq ↦ ?_
    by_cases hfirst : pq ∈ firstLarge p
    · by_cases hpp : pq = (p, p)
      · subst pq
        exact le_sup_left
      · have hadd : pq.1 + pq.2 ≠ 2 * p := by
          intro heq
          have h1 : p ≤ pq.1 := hfirst
          have h2 : p ≤ pq.2 := hpq
          have h : pq.1 = p ∧ pq.2 = p := by lia
          exact hpp (Prod.ext h.1 h.2)
        rw [H.piece_eq_bot_of_add_ne pq.1 pq.2 hadd]
        exact bot_le
    · exact (H.piece_le_pieceSum (s := secondOnly p) (pq := pq)
        ⟨hpq, hfirst⟩).trans le_sup_right
  · refine sup_le ?_ (H.pieceSum_mono Set.sdiff_subset)
    exact H.piece_le_pieceSum (show (p, p) ∈ secondLarge p by simp [secondLarge])

/-- In weight `2p`, the intersection of the ordinary and conjugate `p`-th filtration steps is
exactly the middle Hodge piece. -/
lemma filtration_inf_conjugateFiltration (p : ℕ) (H : Pure V (2 * p)) :
    H.filtration p ⊓ H.conjugateFiltration p = H.piece p p := by
  rw [H.filtration_eq_pieceSum, conjugateFiltration,
    show {pq : ℕ × ℕ | p ≤ pq.1} = firstLarge p from rfl,
    show {pq : ℕ × ℕ | p ≤ pq.2} = secondLarge p from rfl,
    pieceSum_firstLarge p H, pieceSum_secondLarge p H]
  rw [sup_inf_assoc_of_le (H.pieceSum (firstOnly p)) le_sup_left]
  have hdis : Disjoint (H.pieceSum (firstOnly p))
      (H.piece p p ⊔ H.pieceSum (secondOnly p)) := by
    rw [← H.pieceSum_singleton (p, p), ← H.pieceSum_union]
    apply H.disjoint_pieceSum
    exact Set.disjoint_left.mpr fun pq hfirst hsecond ↦ hsecond.elim
      (fun hmiddle ↦ hfirst.2 <| by
        have hpq : pq = (p, p) := by simpa using hmiddle
        subst pq
        simp [secondLarge])
      (fun hsecondOnly ↦ hfirst.2 hsecondOnly.1)
  rw [hdis.eq_bot, sup_bot_eq]

/-- For a rational class in weight `2p`, membership in `F^p` is equivalent to membership in the
middle Hodge piece. Thus the filtration definition of rational Hodge classes agrees with the
usual `(p,p)` definition. -/
lemma ofBase_mem_filtration_iff (p : ℕ) (H : Pure V (2 * p)) (x : V) :
    ofBase ℚ V x ∈ H.filtration p ↔ ofBase ℚ V x ∈ H.piece p p := by
  constructor
  · intro hx
    have hconj : ofBase ℚ V x ∈ H.conjugateFiltration p := by
      rw [← conjugate_ofBase V x]
      exact H.conjugate_mem_filtration p hx
    rw [← H.filtration_inf_conjugateFiltration p]
    exact ⟨hx, hconj⟩
  · exact fun hx ↦ H.piece_le_filtration (p := p) (a := p) (b := p) le_rfl hx

/-- In weight `2p`, taking the inverse image of `F^p` along the rational lattice gives exactly
the usual rational `(p,p)` classes. -/
lemma filtration_comap_ofBase_eq_hodgeClasses (p : ℕ) (H : Pure V (2 * p)) :
    Submodule.comap (ofBase ℚ V) ((H.filtration p).restrictScalars ℚ) =
      hodgeClasses p H := by
  ext x
  exact H.ofBase_mem_filtration_iff p x

end Pure

end HodgeStructure
