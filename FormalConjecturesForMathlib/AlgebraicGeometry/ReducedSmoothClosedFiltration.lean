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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ReducedSmoothStratification

/-!
# The canonical smooth decomposition as a closed filtration

This module indexes the already constructed recursive smooth decomposition by natural
numbers. Consecutive closed supports differ by the actual smooth piece. The filtration
is empty at the length of the existing finite list and stays empty thereafter. This
format exposes precisely the nested closed supports required for localization induction;
it introduces no stratification choices or assumed cohomology vanishing.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

/-- Iteration of the actual reduced singular remainder, padded only by empty supports
after the already constructed finite decomposition terminates. -/
def reducedSmoothClosedFiltration (S : Closeds X) : ℕ → Closeds X
  | 0 => S
  | k + 1 => reducedClosedSingularRemainder f (reducedSmoothClosedFiltration S k)

@[simp] theorem reducedSmoothClosedFiltration_zero (S : Closeds X) :
    reducedSmoothClosedFiltration f S 0 = S := rfl

@[simp] theorem reducedSmoothClosedFiltration_succ (S : Closeds X) (k : ℕ) :
    reducedSmoothClosedFiltration f S (k + 1) =
      reducedClosedSingularRemainder f (reducedSmoothClosedFiltration f S k) := rfl

theorem reducedSmoothClosedFiltration_succ_start (S : Closeds X) (k : ℕ) :
    reducedSmoothClosedFiltration f S (k + 1) =
      reducedSmoothClosedFiltration f (reducedClosedSingularRemainder f S) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [reducedSmoothClosedFiltration_succ, ih, reducedSmoothClosedFiltration_succ]

@[simp] theorem reducedClosedSingularRemainder_bot :
    reducedClosedSingularRemainder f ⊥ = ⊥ :=
  le_bot_iff.mp (reducedClosedSingularRemainder_le f ⊥)

@[simp] theorem reducedSmoothClosedFiltration_bot (k : ℕ) :
    reducedSmoothClosedFiltration f ⊥ k = ⊥ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [reducedSmoothClosedFiltration_succ, ih, reducedClosedSingularRemainder_bot]

theorem reducedSmoothClosedFiltration_succ_le (S : Closeds X) (k : ℕ) :
    reducedSmoothClosedFiltration f S (k + 1) ≤ reducedSmoothClosedFiltration f S k :=
  reducedClosedSingularRemainder_le f _

theorem reducedSmoothClosedFiltration_antitone (S : Closeds X) :
    Antitone (reducedSmoothClosedFiltration f S) :=
  antitone_nat_of_succ_le (reducedSmoothClosedFiltration_succ_le f S)

theorem reducedSmoothClosedFiltration_le (S : Closeds X) (k : ℕ) :
    reducedSmoothClosedFiltration f S k ≤ S :=
  reducedSmoothClosedFiltration_antitone f S (Nat.zero_le k)

/-- Each successive layer is the range of the actual smooth locally closed immersion. -/
theorem reducedSmoothClosedFiltration_layer (S : Closeds X) (k : ℕ) :
    Set.range (reducedClosedSmoothPieceι f (reducedSmoothClosedFiltration f S k)) =
      (reducedSmoothClosedFiltration f S k : Set X) \
        (reducedSmoothClosedFiltration f S (k + 1) : Set X) :=
  reducedClosedSmoothPiece_range f _

variable [PerfectField K] [NoetherianSpace X]

omit [NoetherianSpace X] in
/-- Nonempty steps are strict; no artificial repeated nonempty supports are inserted. -/
theorem reducedSmoothClosedFiltration_succ_lt (S : Closeds X) (k : ℕ)
    (hk : reducedSmoothClosedFiltration f S k ≠ ⊥) :
    reducedSmoothClosedFiltration f S (k + 1) < reducedSmoothClosedFiltration f S k :=
  reducedClosedSingularRemainder_lt f _ hk

/-- The terminal index is the actual finite list length, not supplied termination data. -/
theorem reducedSmoothClosedFiltration_length (S : Closeds X) :
    reducedSmoothClosedFiltration f S (reducedSmoothStratification f S).length = ⊥ := by
  induction S using (wellFounded_lt (α := Closeds X)).induction with
  | h S ih =>
    by_cases hS : S = ⊥
    · subst S
      exact reducedSmoothClosedFiltration_bot f _
    · have hlen : (reducedSmoothStratification f S).length =
          (reducedSmoothStratification f (reducedClosedSingularRemainder f S)).length + 1 := by
        rw [reducedSmoothStratification, dif_neg hS, List.length_cons]
      rw [hlen, reducedSmoothClosedFiltration_succ_start]
      exact ih _ (reducedClosedSingularRemainder_lt f S hS)

/-- Every index at or after the constructed terminal length is empty. -/
theorem reducedSmoothClosedFiltration_eq_bot_of_length_le (S : Closeds X) {k : ℕ}
    (hk : (reducedSmoothStratification f S).length ≤ k) :
    reducedSmoothClosedFiltration f S k = ⊥ := by
  apply le_bot_iff.mp
  rw [← reducedSmoothClosedFiltration_length f S]
  exact reducedSmoothClosedFiltration_antitone f S hk

/-- Every nonterminal support is a member of the already constructed finite list. -/
theorem reducedSmoothClosedFiltration_mem (S : Closeds X) {k : ℕ}
    (hk : k < (reducedSmoothStratification f S).length) :
    reducedSmoothClosedFiltration f S k ∈ reducedSmoothStratification f S := by
  induction k generalizing S with
  | zero =>
    rw [reducedSmoothClosedFiltration_zero, reducedSmoothStratification]
    split_ifs with hS
    · subst S
      simp [reducedSmoothStratification] at hk
    · exact List.mem_cons_self
  | succ k ih =>
    rw [reducedSmoothStratification] at hk ⊢
    split_ifs at hk ⊢ with hS
    · simp at hk
    · rw [List.length_cons, Nat.add_lt_add_iff_right] at hk
      exact List.mem_cons_of_mem _ (by
        rw [reducedSmoothClosedFiltration_succ_start]
        exact ih _ hk)

end AlgebraicGeometry
