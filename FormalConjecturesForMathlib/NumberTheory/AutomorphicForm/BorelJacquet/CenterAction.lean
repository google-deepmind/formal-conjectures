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

public import FormalConjecturesForMathlib.NumberTheory.AutomorphicForm.BorelJacquet.LieDeriv
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.UniversalEnveloping

@[expose] public section

/-!
# The enveloping algebra of `𝔤𝔩 n ℂ`, its centre, and their action

The universal enveloping algebra `U(𝔤𝔩 n ℂ)` of the complexified Lie algebra of `GL n ℝ` and
the action of its centre on the `C^∞` functions on `GL n ℝ` by left invariant differential
operators. This is the action that condition (c) in the Borel-Jacquet definition of an
automorphic form refers to; see
`FormalConjecturesForMathlib.NumberTheory.AutomorphicForm.BorelJacquet` for that definition.

## Main declarations

All in the namespace `Matrix.GeneralLinearGroup`:

* `universalEnveloping` and `centerUniversalEnveloping`: `U(𝔤𝔩 n ℂ)` and its centre.
* `lieDerivHom`, `envelopingAction`, `centerAction`: the action of `𝔤𝔩 n ℂ` on `smoothGL n`
  as a homomorphism of Lie algebras, its extension to `U(𝔤𝔩 n ℂ)` by the universal property,
  and the restriction to the centre, which also makes `smoothGL n` a module over the centre.
* `constantsCharacter`: the character by which the centre acts on the line of constant
  functions; its kernel is an ideal of finite codimension annihilating the constants, which
  gives condition (c) for constant automorphic forms.
-/

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

-- `Matrix n n ℂ` is a Lie ring under the commutator; Mathlib keeps this instance local, since
-- it competes with the bracket of a Lie algebra given abstractly.
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The commutator bracket making `𝔤𝔩 n ℂ = Matrix n n ℂ` a Lie ring, available as
`open scoped Matrix.GeneralLinearGroup`. It agrees with the bracket used by
`Matrix.GeneralLinearGroup.universalEnveloping` below. -/
scoped instance instLieRingMatrixComplex : LieRing (Matrix n n ℂ) :=
  LieRing.ofAssociativeRing

/-- The universal enveloping algebra `U(𝔤𝔩 n ℂ)` of the complexified Lie algebra of `GL n ℝ`.
The complexification of `𝔤𝔩 n ℝ` is `𝔤𝔩 n ℂ = Matrix n n ℂ` with its commutator bracket.

This abbreviation records the choice of `LieRing.ofAssociativeRing` as the bracket, so that
downstream files can name the algebra without re-enabling that local instance. -/
noncomputable abbrev universalEnveloping (n : Type*) [Fintype n] [DecidableEq n] : Type _ :=
  UniversalEnvelopingAlgebra ℂ (Matrix n n ℂ)

/-- The centre of the universal enveloping algebra of the complexified Lie algebra of `GL n ℝ`.
This is the algebra acting in condition (c) in the definition of an automorphic form. -/
noncomputable abbrev centerUniversalEnveloping (n : Type*) [Fintype n] [DecidableEq n] :
    Subalgebra ℂ (universalEnveloping n) :=
  Subalgebra.center ℂ (universalEnveloping n)

/-- The action of `𝔤𝔩 n ℂ` on the `C^∞` functions on `GL n ℝ` by left invariant differential
operators, as a homomorphism of `ℂ`-Lie algebras. -/
noncomputable def lieDerivHom : Matrix n n ℂ →ₗ⁅ℂ⁆ Module.End ℂ (smoothGL n) where
  toFun := lieDerivC
  map_add' := lieDerivC_add
  map_smul' := lieDerivC_smul
  map_lie' {Z W} := by simpa [Ring.lie_def] using lieDerivC_bracket Z W

/-- The action of the universal enveloping algebra `U(𝔤𝔩 n ℂ)` on the `C^∞` functions on
`GL n ℝ`, obtained from `lieDerivHom` by the universal property. A monomial `X₁ ⋯ X_k` acts as
the composite of the corresponding left invariant derivatives. -/
noncomputable def envelopingAction :
    universalEnveloping n →ₐ[ℂ] Module.End ℂ (smoothGL n) :=
  UniversalEnvelopingAlgebra.lift ℂ lieDerivHom

/-- The centre of the universal enveloping algebra acting on the `C^∞` functions on `GL n ℝ`.
Restricting `envelopingAction` to the centre, this is the action condition (c) in the definition
of an automorphic form refers to. -/
noncomputable def centerAction :
    ↥(centerUniversalEnveloping n) →ₐ[ℂ] Module.End ℂ (smoothGL n) :=
  envelopingAction.comp (centerUniversalEnveloping n).val

/-- The `C^∞` functions on `GL n ℝ` as a module over the centre of the universal enveloping
algebra, via left invariant differential operators. -/
noncomputable instance instModuleCenterSmoothGL :
    Module ↥(centerUniversalEnveloping n) (smoothGL n) :=
  Module.compHom (smoothGL n) (centerAction (n := n)).toRingHom

lemma centerAction_smul (z : ↥(centerUniversalEnveloping n)) (φ : smoothGL n) :
    z • φ = centerAction z φ := rfl

instance : SMulCommClass ↥(centerUniversalEnveloping n) ℂ (smoothGL n) where
  smul_comm z c φ := by rw [centerAction_smul, centerAction_smul, map_smul]

instance : IsScalarTower ℂ ↥(centerUniversalEnveloping n) (smoothGL n) where
  smul_assoc c z φ := by
    rw [centerAction_smul, centerAction_smul, map_smul, LinearMap.smul_apply]

/-!
### Constant functions span an invariant line

Left invariant derivatives kill constants, so the enveloping algebra maps the line of constant
functions to itself, through the character `constantsCharacter`; its kernel is an ideal of
finite codimension annihilating the constants.
-/

variable (n) in
/-- The constant function `1` as an element of `smoothGL n`; the constant functions are the
line it spans. -/
def oneSmoothGL : smoothGL n := ⟨fun _ => 1, isSmoothOnGL_const 1⟩

/-- An element of the line of constant functions is determined by its value at `1`. -/
lemma eq_smul_oneSmoothGL_of_mem_span {φ : smoothGL n} (hφ : φ ∈ (ℂ ∙ oneSmoothGL n)) :
    φ = (φ : GL n ℝ → ℂ) 1 • oneSmoothGL n := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hφ
  congr 1
  simp [oneSmoothGL]

/-- Left invariant differential operators map the constant functions to constant functions:
the generators `lieDerivC X` kill them. -/
lemma envelopingAction_mem_span_oneSmoothGL (u : universalEnveloping n) :
    ∀ φ ∈ (ℂ ∙ oneSmoothGL n), envelopingAction u φ ∈ (ℂ ∙ oneSmoothGL n) := by
  have hsurj : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (Matrix n n ℂ)) :=
    RingCon.mkₐ_surjective _
  obtain ⟨t, rfl⟩ := hsurj u
  induction t using TensorAlgebra.induction with
  | algebraMap c =>
    intro φ hφ
    rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply]
    exact Submodule.smul_mem _ c hφ
  | ι X =>
    intro φ hφ
    have hlie : ∀ Y : Matrix n n ℝ, lieDeriv Y (oneSmoothGL n) = 0 := fun Y =>
      Subtype.ext (by simpa [oneSmoothGL] using lieDerivFun_const Y 1)
    have hone : lieDerivC X (oneSmoothGL n) = 0 := by
      simp [lieDerivC, hlie]
    rw [show envelopingAction ((UniversalEnvelopingAlgebra.mkAlgHom ℂ (Matrix n n ℂ))
      ((TensorAlgebra.ι ℂ) X)) = lieDerivC X from UniversalEnvelopingAlgebra.lift_ι_apply' ℂ _ X]
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hφ
    rw [map_smul, hone, smul_zero]
    exact Submodule.zero_mem _
  | mul a b ha hb =>
    intro φ hφ
    rw [map_mul, map_mul, Module.End.mul_apply]
    exact ha _ (hb _ hφ)
  | add a b ha hb =>
    intro φ hφ
    rw [map_add, map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ (ha _ hφ) (hb _ hφ)

lemma smul_oneSmoothGL_mem_span (z : ↥(centerUniversalEnveloping n)) :
    z • oneSmoothGL n ∈ (ℂ ∙ oneSmoothGL n) := by
  rw [centerAction_smul]
  exact envelopingAction_mem_span_oneSmoothGL (z : universalEnveloping n) _
    (Submodule.mem_span_singleton_self _)

variable (n) in
/-- The character by which the centre of the enveloping algebra acts on the constant
functions: `z • 1 = constantsCharacter n z • 1`. Its kernel is an ideal of finite codimension
annihilating the constants, which gives condition (c) for constant automorphic forms. -/
noncomputable def constantsCharacter : ↥(centerUniversalEnveloping n) →ₐ[ℂ] ℂ where
  toFun z := ((z • oneSmoothGL n : smoothGL n) : GL n ℝ → ℂ) 1
  map_one' := by rw [one_smul]; simp [oneSmoothGL]
  map_mul' z w := by
    rw [mul_smul, eq_smul_oneSmoothGL_of_mem_span (smul_oneSmoothGL_mem_span w),
      smul_comm z, Submodule.coe_smul, Pi.smul_apply]
    simp [oneSmoothGL, mul_comm]
  map_zero' := by rw [zero_smul]; simp
  map_add' z w := by rw [add_smul]; simp
  commutes' c := by
    rw [algebraMap_smul, Submodule.coe_smul, Pi.smul_apply]
    simp [oneSmoothGL]

end Matrix.GeneralLinearGroup
