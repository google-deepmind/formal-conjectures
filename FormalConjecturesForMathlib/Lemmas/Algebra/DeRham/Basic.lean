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

public import FormalConjecturesForMathlib.Definitions.Algebra.DeRham.Basic

/-!
# Algebraic de Rham forms

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.Algebra.DeRham.Basic`.
-/

@[expose] public noncomputable section

universe u

namespace Algebra.DeRham

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

variable {R A}

variable (R A)

namespace Sq

variable {R A}

end Sq

namespace Sq

variable {R A}

end Sq

namespace Sq

end Sq

lemma deRhamHom_apply (x : ExtAlg R A) :
    deRhamHom R A x = Sq.mk x (extDeriv R A x) := by
  ext
  · simp
  · rfl

/-- The exterior derivative anticommutes with the grade involution, since it raises the degree
by one. -/
lemma extDeriv_involute (x : ExtAlg R A) :
    extDeriv R A (involute R A x) = -involute R A (extDeriv R A x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => simp
  | ι ω => simp [involute_snd_phi]
  | mul x y hx hy =>
      rw [map_mul, extDeriv_mul, hx, hy, extDeriv_mul, map_add, map_mul, map_mul,
        CliffordAlgebra.involute_involute]
      simp only [mul_neg, neg_mul, neg_add]
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]

lemma extDeriv_snd_phi (ω : Ω[A⁄R]) : extDeriv R A (Sq.snd (phi R A ω)) = 0 := by
  induction ω using D_induction with
  | D a => simp
  | zero => simp
  | add x y hx hy => rw [map_add, Sq.snd_add, map_add, hx, hy, add_zero]
  | smul a x hx =>
      rw [snd_phi_smul, map_add, Algebra.smul_def, extDeriv_mul, extDeriv_mul, hx,
        involute_algebraMap, extDeriv_algebraMap, mul_zero, zero_add, involute_ι]
      simp only [extDeriv_ι, phi_D, Sq.snd_mk, zero_mul, add_zero, neg_mul]
      abel

/-- The exterior derivative squares to zero. -/
lemma extDeriv_extDeriv (x : ExtAlg R A) : extDeriv R A (extDeriv R A x) = 0 := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => simp
  | ι ω => rw [extDeriv_ι]; exact extDeriv_snd_phi R A ω
  | mul x y hx hy =>
      rw [extDeriv_mul, map_add, extDeriv_mul, extDeriv_mul, hx, hy, extDeriv_involute,
        CliffordAlgebra.involute_involute]
      simp only [mul_zero, zero_mul, neg_mul, zero_add, add_zero, neg_add_cancel]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

lemma differential_squared (p : ℕ) (x : Form R A p) :
    differential R A (p + 1) (differential R A p x) = 0 :=
  Subtype.ext (extDeriv_extDeriv R A x)

/-! ### Functoriality -/

section Tower

variable (B : Type u) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

lemma extAlgMap_involute (x : ExtAlg R A) :
    extAlgMap R A B (involute R A x) = involute R B (extAlgMap R A B x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => simp
  | ι ω => simp
  | mul x y hx hy => simp only [map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma extAlgMap_snd_phi (ω : Ω[A⁄R]) :
    extAlgMap R A B (Sq.snd (phi R A ω)) =
      Sq.snd (phi R B (KaehlerDifferential.map R R A B ω)) := by
  induction ω using D_induction with
  | D a => simp
  | zero => simp
  | add x y hx hy => simp only [map_add, Sq.snd_add, hx, hy]
  | smul a x hx =>
      rw [snd_phi_smul, map_add, map_smul, hx, map_mul, extAlgMap_ι, extAlgMap_ι,
        KaehlerDifferential.map_D, map_smul,
        ← algebraMap_smul (R := A) B a (KaehlerDifferential.map R R A B x), snd_phi_smul,
        ← algebraMap_smul (R := A) B a (Sq.snd (phi R B (KaehlerDifferential.map R R A B x)))]

lemma extAlgMap_extDeriv (x : ExtAlg R A) :
    extAlgMap R A B (extDeriv R A x) = extDeriv R B (extAlgMap R A B x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a =>
      rw [extDeriv_algebraMap, extAlgMap_ι, KaehlerDifferential.map_D, extAlgMap_algebraMap,
        extDeriv_algebraMap]
  | ι ω => rw [extDeriv_ι, extAlgMap_snd_phi, extAlgMap_ι, extDeriv_ι]
  | mul x y hx hy =>
      rw [extDeriv_mul, map_add, map_mul, map_mul, hx, hy, extAlgMap_involute, map_mul,
        extDeriv_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Tower

section AlgHomMap

variable {A}
variable {B C : Type u} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

lemma map_differential (f : A →ₐ[R] B) (p : ℕ) (x : Form R A p) :
    map R f (p + 1) (differential R A p x) = differential R B p (map R f p x) := by
  let _ := f.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  exact Subtype.ext (extAlgMap_extDeriv R A B x)

end AlgHomMap

end Algebra.DeRham
