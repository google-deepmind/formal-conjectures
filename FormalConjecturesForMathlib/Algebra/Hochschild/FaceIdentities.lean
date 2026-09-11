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

public import FormalConjecturesForMathlib.Algebra.Hochschild.FaceFormulas

/-!
# Hochschild face identities

This file proves the face-composition identities for the concrete Hochschild tensor faces.
-/

@[expose] public section

namespace Hochschild

variable {A : Type*} [NonUnitalRing A]

/-- An ordinary face commutes past the cyclic last face in the indicated simplicial identity. -/
theorem standardFaceTuple_comp_last_of_lt (n : ℕ) (i : Fin (n + 3))
    (hi : i.val < n + 1) (x : Fin (n + 3) → A) :
    let i' : Fin (n + 2) := ⟨i.val, by omega⟩
    standardFaceTuple A n i'
        (standardFaceTuple A (n + 1) (Fin.last (n + 2)) x) =
      standardFaceTuple A n (Fin.last (n + 1))
        (standardFaceTuple A (n + 1) i x) := by
  let i' : Fin (n + 2) := ⟨i.val, by omega⟩
  dsimp only
  have hi'_last : i' ≠ Fin.last (n + 1) := by
    intro he
    have := congrArg Fin.val he
    simp [i'] at this
    omega
  have hi_last : i ≠ Fin.last (n + 2) := by
    intro he
    have := congrArg Fin.val he
    simp at this
    omega
  let ii : Fin (n + 1) := i'.castPred hi'_last
  let ip : Fin (n + 2) := i.castPred hi_last
  have hip_le_last : ip ≤ Fin.last (n + 1) := Fin.le_last _
  have hip_ne_last : Fin.last (n + 1) ≠ ip := by
    intro he
    have := congrArg Fin.val he
    simp [ip] at this
    omega
  funext q
  refine Fin.cases ?_ (fun r ↦ ?_) q
  · by_cases hi0 : i = 0
    · subst i
      simp [standardFaceTuple, mul_assoc]
    · have hii_pos : (0 : Fin (n + 1)) < ii := by
        rw [Fin.pos_iff_ne_zero]
        intro hz
        apply hi0
        apply Fin.ext
        simpa [ii, i'] using congrArg Fin.val hz
      have hip_pos : (0 : Fin (n + 2)) < ip := by
        rw [Fin.lt_def]
        simp only [Fin.val_zero]
        have hiv : i.val ≠ 0 := by
          intro hz
          apply hi0
          apply Fin.ext
          simpa using hz
        simpa [ip] using Nat.pos_of_ne_zero hiv
      simp [standardFaceTuple, i', ii, ip, hi'_last, hi_last, hii_pos, hip_pos,
        hip_le_last, hip_ne_last]
  · by_cases hi0 : i = 0
    · subst i
      simp [standardFaceTuple]
    · by_cases hlt : r.succ < ii
      all_goals
        have hip_pos : (0 : Fin (n + 2)) < ip := by
          rw [Fin.lt_def]
          simp only [Fin.val_zero]
          have hiv : i.val ≠ 0 := by
            intro hz
            apply hi0
            apply Fin.ext
            simpa using hz
          simpa [ip] using Nat.pos_of_ne_zero hiv
      · have hlt' : r.castSucc.succ < i.castPred hi_last := by
          simpa [ii, i', Fin.lt_def] using hlt
        simp [standardFaceTuple, i', ii, hi'_last, hi_last, hlt, hlt']
      · by_cases heq : r.succ = ii
        · have heq' : r.castSucc.succ = i.castPred hi_last := by
            apply Fin.ext
            simpa [ii, i'] using congrArg Fin.val heq
          have hi'0 : i' ≠ 0 := by
            intro hz
            apply hi0
            apply Fin.ext
            simpa [i'] using congrArg Fin.val hz
          have heval :
              Fin.cons (α := fun _ : Fin (n + 2) ↦ A) (x (Fin.last (n + 2)) * x 0)
                (fun q => x q.castSucc.succ) i' = x i := by
            rw [← Fin.succ_pred i' hi'0, Fin.cons_succ]
            apply congrArg x
            apply Fin.ext
            have hp := congrArg Fin.val (Fin.succ_pred i' hi'0)
            simp only [Fin.val_succ, Fin.val_castSucc] at hp ⊢
            exact hp.trans (by rfl)
          simp [standardFaceTuple, i', ii, hi'_last, hi_last, heq.symm, heq', heval]
        · have hlt' : ¬r.castSucc.succ < i.castPred hi_last := by
            simpa [ii, i', Fin.lt_def] using hlt
          have heq' : r.castSucc.succ ≠ i.castPred hi_last := by
            intro he
            apply heq
            apply Fin.ext
            simpa [ii, i'] using congrArg Fin.val he
          simp [standardFaceTuple, i', ii, hi'_last, hi_last, hlt, heq, hlt', heq']


variable (A)

/-- The face identity involving the last two positions, from associativity. -/
theorem standardFaceTuple_double_last (n : ℕ) (x : Fin (n + 3) → A) :
    standardFaceTuple A n (Fin.last (n + 1))
        (standardFaceTuple A (n + 1) (Fin.last (n + 2)) x) =
      standardFaceTuple A n (Fin.last (n + 1))
        (standardFaceTuple A (n + 1) (Fin.castSucc (Fin.last (n + 1))) x) := by
  funext q
  have hi : Fin.castSucc (Fin.last (n + 1)) ≠ Fin.last (n + 2) := by simp
  simp only [standardFaceTuple, hi, ↓reduceDIte]
  refine Fin.cases ?_ (fun j ↦ ?_) q
  · simp [Fin.cons_last, Fin.lt_def, mul_assoc]
    congr 2
  · simp [Fin.lt_def]

variable {A}

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
/-- The face-face identity when the later face is not cyclic. -/
theorem standardFaceTuple_comp_of_ne_last (n : ℕ) (i : Fin (n + 3)) (j : Fin (n + 2))
    (H : i ≤ Fin.castSucc j) (hj : j ≠ Fin.last (n + 1)) (x : Fin (n + 3) → A) :
    standardFaceTuple A n
        (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt))
        (standardFaceTuple A (n + 1) j.succ x) =
      standardFaceTuple A n j (standardFaceTuple A (n + 1) i x) := by
  have hij : i.val ≤ j.val := Fin.le_iff_val_le_val.mp H
  have hjv : j.val < n + 1 := by
    have hjle : j.val ≤ n + 1 := Nat.le_of_lt_succ j.is_lt
    have hjne : j.val ≠ n + 1 := by
      intro h
      apply hj
      ext
      simpa using h
    omega
  have hi : i ≠ Fin.last (n + 2) := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hjs : j.succ ≠ Fin.last (n + 2) := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  let i' := i.castLT (Nat.lt_of_le_of_lt hij j.is_lt)
  have hi' : i' ≠ Fin.last (n + 1) := by
    intro h
    have := congrArg Fin.val h
    simp [i'] at this
    omega
  funext q
  change standardFaceTuple A n i' (standardFaceTuple A (n + 1) j.succ x) q =
    standardFaceTuple A n j (standardFaceTuple A (n + 1) i x) q
  simp only [standardFaceTuple, dif_neg hi', dif_neg hjs, dif_neg hj, dif_neg hi]
  dsimp only [i'] at *
  simp only [Fin.lt_def, Fin.ext_iff, Fin.val_castLT, Fin.val_castSucc, Fin.val_succ,
    Fin.coe_castPred] at *
  split_ifs <;> try omega
  all_goals try simp only [mul_assoc]
  all_goals try rfl
  all_goals
    congr 3
    simp only [Fin.ext_iff, Fin.val_succ, Fin.coe_castPred] at *
    omega


/-- The usual Hochschild faces satisfy the simplicial face identity. -/
theorem standardFaceTuple_comp (n : ℕ) (i : Fin (n + 3)) (j : Fin (n + 2))
    (H : i ≤ Fin.castSucc j) (x : Fin (n + 3) → A) :
    standardFaceTuple A n
        (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt))
        (standardFaceTuple A (n + 1) j.succ x) =
      standardFaceTuple A n j (standardFaceTuple A (n + 1) i x) := by
  by_cases hj : j = Fin.last (n + 1)
  · subst j
    have hi : i.val ≤ n + 1 := Fin.le_iff_val_le_val.mp H
    by_cases he : i.val = n + 1
    · have he' : i = Fin.castSucc (Fin.last (n + 1)) := by
        apply Fin.ext
        exact he
      subst i
      exact standardFaceTuple_double_last A n x
    · exact standardFaceTuple_comp_last_of_lt n i (by omega) x
  · exact standardFaceTuple_comp_of_ne_last n i j H hj x

variable (k : Type*) [CommRing k] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A]

/-- The concrete tensor-power Hochschild faces satisfy the simplicial face identity. -/
theorem face_comp_face (n : ℕ) (i : Fin (n + 3)) (j : Fin (n + 2))
    (H : i ≤ Fin.castSucc j) :
    face k A n (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) ∘ₗ
        face k A (n + 1) j.succ =
      face k A n j ∘ₗ face k A (n + 1) i := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change face k A n _ (face k A (n + 1) _ (PiTensorProduct.tprod k x)) =
    face k A n _ (face k A (n + 1) _ (PiTensorProduct.tprod k x))
  simp only [face_tprod_standard]
  exact congrArg (PiTensorProduct.tprod k) (standardFaceTuple_comp n i j H x)

end Hochschild
