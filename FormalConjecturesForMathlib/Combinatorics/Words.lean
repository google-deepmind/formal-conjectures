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

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Equiv.Basic

@[expose] public section

variable {A : Type*} {B : Type*}

/-- The **block complexity** of a configuration `x : ℤ × ℤ → A` at scale `n × m` is the number
of distinct `n × m` rectangular patterns appearing in `x`. -/
noncomputable def blockComplexity (x : ℤ × ℤ → A) (n m : ℕ) : ℕ :=
  (Set.range fun (p : ℤ × ℤ) => fun (q : Fin n × Fin m) =>
    x (p.1 + (q.1 : ℤ), p.2 + (q.2 : ℤ))).ncard

/-- A configuration `x : ℤ × ℤ → A` is **periodic** if there exists a nonzero vector
`v : ℤ × ℤ` such that translating by `v` leaves `x` invariant. -/
def IsPeriodic (x : ℤ × ℤ → A) : Prop :=
  ∃ v : ℤ × ℤ, v ≠ 0 ∧ Function.Periodic x v

/-- The block complexity of a configuration does not depend on the names of the letters. -/
@[simp]
theorem blockComplexity_equiv_comp (e : A ≃ B) (x : ℤ × ℤ → A) (n m : ℕ) :
    blockComplexity (e ∘ x) n m = blockComplexity x n m := by
  have hinj : Function.Injective (fun (φ : Fin n × Fin m → A) => e ∘ φ) :=
    fun _ _ h => funext fun q => e.injective (congrFun h q)
  unfold blockComplexity
  rw [show (fun (p : ℤ × ℤ) => fun (q : Fin n × Fin m) =>
        (e ∘ x) (p.1 + (q.1 : ℤ), p.2 + (q.2 : ℤ)))
      = (fun (φ : Fin n × Fin m → A) => e ∘ φ) ∘
        (fun (p : ℤ × ℤ) => fun (q : Fin n × Fin m) =>
          x (p.1 + (q.1 : ℤ), p.2 + (q.2 : ℤ))) from rfl,
    Set.range_comp, Set.ncard_image_of_injective _ hinj]

/-- Periodicity of a configuration does not depend on the names of the letters. -/
@[simp]
theorem isPeriodic_equiv_comp (e : A ≃ B) (x : ℤ × ℤ → A) :
    IsPeriodic (e ∘ x) ↔ IsPeriodic x :=
  exists_congr fun _ => and_congr_right fun _ =>
    forall_congr' fun _ => e.apply_eq_iff_eq
