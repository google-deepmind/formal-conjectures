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

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# Alternating complexes from face data

This file constructs a chain complex from a graded family of objects and face maps satisfying
the face-face simplicial identity. Degeneracy maps and the other simplicial identities are not
needed for this construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Preadditive

noncomputable section

namespace AlgebraicTopology.AlternatingFaceMapComplex

variable {C : Type*} [Category* C] [Preadditive C]

/-- A graded family with face maps satisfying the identity needed for the alternating boundary
to square to zero. -/
structure FaceData where
  /-- The object in each homological degree. -/
  X : ℕ → C
  /-- The face maps from degree `n + 1` to degree `n`. -/
  face : ∀ n, Fin (n + 2) → (X (n + 1) ⟶ X n)
  /-- The face-face identity, in the indexing form used by the cancellation proof. -/
  face_comp_face : ∀ (n : ℕ) (i : Fin (n + 3)) (j : Fin (n + 2))
    (H : i ≤ Fin.castSucc j),
      face (n + 1) j.succ ≫
          face n (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) =
        face (n + 1) i ≫ face n j

namespace FaceData

variable (F : FaceData (C := C))

/-- The alternating sum of the faces. -/
def d (n : ℕ) : F.X (n + 1) ⟶ F.X n :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • F.face n i

/-- The alternating boundary squares to zero. -/
theorem d_squared (n : ℕ) : F.d (n + 1) ≫ F.d n = 0 := by
  dsimp [d]
  simp only [comp_sum, sum_comp, ← Finset.sum_product']
  let P := Fin (n + 2) × Fin (n + 3)
  let S : Finset P := {ij : P | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.1)),
      ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    lia
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using! congr_arg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using! congr_arg Fin.castSucc (congr_arg Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred <| ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij'
    · simpa [S] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, pow_add, pow_one, mul_neg, neg_neg, mul_one]
      apply mul_comm
    · rw [F.face_comp_face]
      simpa [S] using! hij

/-- The chain complex whose differential is the alternating sum of the faces. -/
@[implicit_reducible]
def chainComplex : ChainComplex C ℕ :=
  ChainComplex.of F.X F.d F.d_squared

@[simp] theorem chainComplex_X (n : ℕ) : F.chainComplex.X n = F.X n := rfl

@[simp] theorem chainComplex_d (n : ℕ) : F.chainComplex.d (n + 1) n = F.d n := by
  simp [chainComplex]

end FaceData

end AlgebraicTopology.AlternatingFaceMapComplex
