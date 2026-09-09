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

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-!
# Lie derivatives of smooth functions on `GL n ℝ`

The `C^∞` functions on `GL n ℝ` and the action on them of `𝔤𝔩 n ℝ` and of its
complexification `𝔤𝔩 n ℂ` by left invariant differential operators. This is the analytic
machinery behind condition (c) in the Borel-Jacquet definition of an automorphic form; see
`FormalConjecturesForMathlib.NumberTheory.AutomorphicForm.BorelJacquet` for that definition.

## Main declarations

All in the namespace `Matrix.GeneralLinearGroup` unless qualified otherwise:

* `AutomorphicForm.LieDerivAux.fderiv_rightDeriv_apply` and `…_sub_comm`: the product rule and
  bracket identity for the operator `F ↦ fun M => fderiv ℝ F M (M * X)` over an abstract
  normed algebra.
* `IsSmoothOnGL` and `smoothGL`: the `C^∞` functions on `GL n ℝ`, as a predicate and as a
  `ℂ`-submodule.
* `expGL` and `lieDerivFun`: the matrix exponential as an element of `GL n ℝ`, and the left
  invariant derivative `(X • φ) y = d/dt φ (y * exp (t • X)) |_{t = 0}`.
* `lieDeriv` and `lieDerivC`: the actions on `smoothGL n` of `𝔤𝔩 n ℝ` and of its
  complexification `𝔤𝔩 n ℂ`, with their bracket identities `lieDeriv_bracket` and
  `lieDerivC_bracket`.

## Implementation notes

Smoothness on `GL n ℝ` is phrased as the existence of a `C^∞` extension to the open set of
invertible matrices (`IsSmoothOnGL`), rather than through a manifold structure: the normed
ring instances on `Matrix n n ℝ` that would give `GL n ℝ` a chart are scoped, and conflict
with the product topology that `GL n ℝ` already carries.

`X ∈ 𝔤𝔩 n ℝ` acts by differentiating along the one-parameter subgroup,
`(X • φ) y = d/dt φ (y * exp (t • X)) |_{t = 0}`; this equals `fderiv ℝ F y (y * X)` for any
`C^∞` extension `F` of `φ` (`lieDerivFun_eq_fderiv`), through which every algebraic property
is proved. The bracket identity is the product rule plus symmetry of the second derivative.

The product rule is proved over an abstract finite-dimensional normed `ℝ`-algebra and
instantiated at `Matrix n n ℝ`. That is forced: Mathlib's norms on `Matrix n n ℝ` are scoped
instances while its topology is global, so instance search cannot assemble
`SeminormedAddCommGroup (Matrix n n ℝ →L[ℝ] ℂ)` for the written-out type even though the
instance term typechecks, and the second-derivative lemmas behind the product rule need that
instance as an argument. Instantiating an abstract lemma supplies its instance arguments
instead of searching for them.
-/

open scoped ContDiff

/-!
### The product rule, over an abstract normed algebra

In a group of units, left translation is the restriction of a linear map, so the left
invariant vector field with value `X` at `1` has value `M * X` at `M`, and the first-order
operator is `F ↦ fun M => fderiv ℝ F M (M * X)` — no manifold structure needed. This section
proves its product rule and bracket identity over an abstract algebra `A`; see the
implementation notes for why `A` cannot simply be `Matrix n n ℝ`.
-/

namespace AutomorphicForm.LieDerivAux

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [FiniteDimensional ℝ A]

/-- Right multiplication by `X`, as a continuous linear map. -/
noncomputable def mulRightL (X : A) : A →L[ℝ] A :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

@[simp]
lemma mulRightL_apply (X M : A) : mulRightL X M = M * X := by simp [mulRightL]

/-- The product rule for the left invariant derivative `F ↦ fun M => D F M (M * X)`: its
derivative at `y` in the direction `v` picks up the first-order term `D F y (v * X)`, from
differentiating `M ↦ M * X`, and the second-order term `D² F y v (y * X)`. -/
lemma fderiv_rightDeriv_apply {F : A → ℂ} {y : A} (hF : ContDiffAt ℝ ∞ F y) (X v : A) :
    fderiv ℝ (fun M => fderiv ℝ F M (M * X)) y v
      = fderiv ℝ F y (v * X) + fderiv ℝ (fderiv ℝ F) y v (y * X) := by
  have h₁ : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) y) y :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have h₂ : HasFDerivAt (fun M : A => M * X) (mulRightL X) y := (mulRightL X).hasFDerivAt
  have h₃ := ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := A) (F := ℂ)).hasFDerivAt
    (fderiv ℝ F y, y * X)).comp y (h₁.prodMk h₂)
  have h₄ : HasFDerivAt (fun M : A => fderiv ℝ F M (M * X)) _ y := h₃
  rw [h₄.fderiv]
  simp [IsBoundedBilinearMap.deriv_apply]

/-- The commutator of two left invariant derivatives is the left invariant derivative along
the commutator: the second-order terms cancel by symmetry of the second derivative. -/
lemma fderiv_rightDeriv_sub_comm {F : A → ℂ} {y : A} (hF : ContDiffAt ℝ ∞ F y) (X Y : A) :
    fderiv ℝ (fun M => fderiv ℝ F M (M * Y)) y (y * X)
      - fderiv ℝ (fun M => fderiv ℝ F M (M * X)) y (y * Y)
      = fderiv ℝ F y (y * (X * Y - Y * X)) := by
  have hle : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top
  have hsymm := (hF.isSymmSndFDerivAt hle).eq (y * X) (y * Y)
  rw [fderiv_rightDeriv_apply hF Y (y * X), fderiv_rightDeriv_apply hF X (y * Y),
    show y * (X * Y - Y * X) = y * X * Y - y * Y * X by noncomm_ring, map_sub]
  linear_combination hsymm

end AutomorphicForm.LieDerivAux

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Smooth functions on `GL n ℝ` -/

section Smooth

open scoped Matrix.Norms.Frobenius

/-- `φ : GL n ℝ → ℂ` is `C^∞`: it extends to a `C^∞` function on the open set of invertible
matrices. Stating it this way avoids putting a manifold structure on `GL n ℝ`. -/
def IsSmoothOnGL (φ : GL n ℝ → ℂ) : Prop :=
  ∃ F : Matrix n n ℝ → ℂ, ContDiffOn ℝ ∞ F {M : Matrix n n ℝ | IsUnit M} ∧
    ∀ y : GL n ℝ, F (y : Matrix n n ℝ) = φ y

lemma isSmoothOnGL_const (c : ℂ) : IsSmoothOnGL (fun _ : GL n ℝ => c) :=
  ⟨fun _ => c, contDiffOn_const, fun _ => rfl⟩

lemma IsSmoothOnGL.add {φ ψ : GL n ℝ → ℂ} (hφ : IsSmoothOnGL φ) (hψ : IsSmoothOnGL ψ) :
    IsSmoothOnGL (φ + ψ) := by
  obtain ⟨F, hF, hFφ⟩ := hφ
  obtain ⟨G, hG, hGψ⟩ := hψ
  exact ⟨F + G, ContDiffOn.add hF hG, fun y => by simp [hFφ, hGψ]⟩

lemma IsSmoothOnGL.const_smul {φ : GL n ℝ → ℂ} (hφ : IsSmoothOnGL φ) (c : ℂ) :
    IsSmoothOnGL (c • φ) := by
  obtain ⟨F, hF, hFφ⟩ := hφ
  exact ⟨c • F, ContDiffOn.const_smul c hF, fun y => by simp [hFφ]⟩

/-- The invertible matrices are an open set: they are the nonvanishing locus of `det`. -/
lemma isOpen_setOf_isUnit : IsOpen {M : Matrix n n ℝ | IsUnit M} := by
  have h : {M : Matrix n n ℝ | IsUnit M}
      = (fun M : Matrix n n ℝ => M.det) ⁻¹' {x : ℝ | x ≠ 0} := by
    ext M
    simp [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  rw [h]
  exact isOpen_ne.preimage (by fun_prop)

lemma isUnit_coe (y : GL n ℝ) : IsUnit (y : Matrix n n ℝ) := ⟨y, rfl⟩

/-- A choice of `C^∞` extension of `φ` to the invertible matrices, when one exists. Only its
germ at each invertible matrix matters, by `fderiv_extendGL_eq`. -/
noncomputable def extendGL (φ : GL n ℝ → ℂ) : Matrix n n ℝ → ℂ :=
  haveI := Classical.propDecidable (IsSmoothOnGL φ)
  if h : IsSmoothOnGL φ then h.choose else 0

lemma contDiffOn_extendGL {φ : GL n ℝ → ℂ} (hφ : IsSmoothOnGL φ) :
    ContDiffOn ℝ ∞ (extendGL φ) {M : Matrix n n ℝ | IsUnit M} := by
  rw [extendGL, dif_pos hφ]
  exact hφ.choose_spec.1

@[simp]
lemma extendGL_coe {φ : GL n ℝ → ℂ} (hφ : IsSmoothOnGL φ) (y : GL n ℝ) :
    extendGL φ (y : Matrix n n ℝ) = φ y := by
  rw [extendGL, dif_pos hφ]
  exact hφ.choose_spec.2 y

lemma contDiffAt_extendGL {φ : GL n ℝ → ℂ} (hφ : IsSmoothOnGL φ) (y : GL n ℝ) :
    ContDiffAt ℝ ∞ (extendGL φ) (y : Matrix n n ℝ) :=
  (contDiffOn_extendGL hφ).contDiffAt (isOpen_setOf_isUnit.mem_nhds (isUnit_coe y))

/-- The derivative of the chosen extension at an invertible matrix does not depend on the
choice: any two extensions of `φ` agree on the open set of invertible matrices. -/
lemma fderiv_extendGL_eq {φ : GL n ℝ → ℂ} {F : Matrix n n ℝ → ℂ} (hφ : IsSmoothOnGL φ)
    (hF : ∀ y : GL n ℝ, F (y : Matrix n n ℝ) = φ y) (y : GL n ℝ) :
    fderiv ℝ (extendGL φ) (y : Matrix n n ℝ) = fderiv ℝ F (y : Matrix n n ℝ) := by
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [isOpen_setOf_isUnit.mem_nhds (isUnit_coe y)] with M hM
  obtain ⟨u, rfl⟩ := hM
  rw [extendGL_coe hφ, hF]

/-!
#### Left invariant derivatives

`(X • φ) y = d/dt φ (y * exp (t • X)) |_{t = 0}`, proved equal to the directional derivative
`fderiv ℝ F y (y * X)` of any smooth extension `F` (`lieDerivFun_eq_fderiv`), which is the
form all its properties are established in.
-/

/-- The exponential of a matrix, as an element of `GL n ℝ`: `exp X` is invertible with
inverse `exp (-X)`. -/
noncomputable def expGL (X : Matrix n n ℝ) : GL n ℝ := (NormedSpace.isUnit_exp X).unit

@[simp]
lemma coe_expGL (X : Matrix n n ℝ) : (expGL X : Matrix n n ℝ) = NormedSpace.exp X :=
  (NormedSpace.isUnit_exp X).unit_spec

@[simp]
lemma expGL_zero : expGL (0 : Matrix n n ℝ) = 1 := Units.ext (by simp)

/-- The left invariant derivative of `φ` along `X`: differentiate `φ` along the one-parameter
subgroup `t ↦ exp (t • X)` acting on the right,

`(X • φ) y = d/dt φ (y * exp (t • X)) |_{t = 0}`.

This is the derivative that condition (c) of the definition of an automorphic form is about:
the left invariant vector field with value `X` at `1` has value `y * X` at `y`, and
`lieDerivFun_eq_fderiv` identifies the two descriptions for `C^∞` functions. -/
noncomputable def lieDerivFun (X : Matrix n n ℝ) (φ : GL n ℝ → ℂ) (y : GL n ℝ) : ℂ :=
  deriv (fun t : ℝ => φ (y * expGL (t • X))) 0

/-- Differentiating along the one-parameter subgroup computes the derivative of any smooth
extension in the direction `y * X`. -/
lemma hasDerivAt_lieDerivFun {φ : GL n ℝ → ℂ} (hφ : IsSmoothOnGL φ) (X : Matrix n n ℝ)
    (y : GL n ℝ) :
    HasDerivAt (fun t : ℝ => φ (y * expGL (t • X)))
      (fderiv ℝ (extendGL φ) (y : Matrix n n ℝ) ((y : Matrix n n ℝ) * X)) 0 := by
  -- The instance arguments on `Matrix n n ℝ` are deliberately never written out here: see the
  -- implementation notes. Every one of them arrives by unification from a Mathlib lemma.
  have hexp := (hasDerivAt_exp_smul_const X (0 : ℝ)).const_mul (y : Matrix n n ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hexp
  have hfun : (fun t : ℝ => φ (y * expGL (t • X)))
      = fun t : ℝ => extendGL φ ((y : Matrix n n ℝ) * NormedSpace.exp (t • X)) := by
    funext t
    rw [← extendGL_coe hφ (y * expGL (t • X))]
    simp
  rw [hfun]
  exact HasFDerivAt.comp_hasDerivAt_of_eq
    (hl := ((contDiffAt_extendGL hφ y).differentiableAt (by simp)).hasFDerivAt)
    (hf := hexp) (hy := by simp)

/-- The one-parameter-subgroup description of the left invariant derivative agrees with the
directional-derivative one. Every algebraic property below is proved through this bridge. -/
lemma lieDerivFun_eq_fderiv {φ : GL n ℝ → ℂ} (hφ : IsSmoothOnGL φ) (X : Matrix n n ℝ)
    (y : GL n ℝ) :
    lieDerivFun X φ y
      = fderiv ℝ (extendGL φ) (y : Matrix n n ℝ) ((y : Matrix n n ℝ) * X) :=
  (hasDerivAt_lieDerivFun hφ X y).deriv

lemma IsSmoothOnGL.lieDerivFun {φ : GL n ℝ → ℂ} (hφ : IsSmoothOnGL φ) (X : Matrix n n ℝ) :
    IsSmoothOnGL (lieDerivFun X φ) := by
  refine ⟨fun M => fderiv ℝ (extendGL φ) M (M * X), fun M hM => ?_,
    fun y => (lieDerivFun_eq_fderiv hφ X y).symm⟩
  have h : ContDiffAt ℝ ∞ (extendGL φ) M :=
    (contDiffOn_extendGL hφ).contDiffAt (isOpen_setOf_isUnit.mem_nhds hM)
  exact (((h.fderiv_right (m := ∞) (by simp)).clm_apply
    (contDiffAt_id.mul contDiffAt_const))).contDiffWithinAt

/-- The `ℂ`-submodule of `C^∞` functions on `GL n ℝ`, which is what the Lie algebra and hence
the universal enveloping algebra acts on. -/
def smoothGL (n : Type*) [Fintype n] [DecidableEq n] : Submodule ℂ (GL n ℝ → ℂ) where
  carrier := {φ | IsSmoothOnGL φ}
  zero_mem' := isSmoothOnGL_const 0
  add_mem' hφ hψ := hφ.add hψ
  smul_mem' c _ hφ := hφ.const_smul c

@[simp]
lemma mem_smoothGL {φ : GL n ℝ → ℂ} : φ ∈ smoothGL n ↔ IsSmoothOnGL φ := Iff.rfl

lemma lieDerivFun_add {φ ψ : GL n ℝ → ℂ} (hφ : IsSmoothOnGL φ) (hψ : IsSmoothOnGL ψ)
    (X : Matrix n n ℝ) : lieDerivFun X (φ + ψ) = lieDerivFun X φ + lieDerivFun X ψ := by
  funext y
  have hadd : fderiv ℝ (extendGL φ + extendGL ψ) (y : Matrix n n ℝ)
      = fderiv ℝ (extendGL φ) (y : Matrix n n ℝ) + fderiv ℝ (extendGL ψ) (y : Matrix n n ℝ) :=
    ((((contDiffAt_extendGL hφ y).differentiableAt (by simp)).hasFDerivAt).add
      (((contDiffAt_extendGL hψ y).differentiableAt (by simp)).hasFDerivAt)).fderiv
  rw [lieDerivFun_eq_fderiv (hφ.add hψ), fderiv_extendGL_eq (hφ.add hψ)
    (F := extendGL φ + extendGL ψ)
    (fun z => by simp [extendGL_coe hφ, extendGL_coe hψ]) y, hadd]
  simp [lieDerivFun_eq_fderiv hφ, lieDerivFun_eq_fderiv hψ]

lemma lieDerivFun_const_smul {φ : GL n ℝ → ℂ} (hφ : IsSmoothOnGL φ) (c : ℂ)
    (X : Matrix n n ℝ) : lieDerivFun X (c • φ) = c • lieDerivFun X φ := by
  funext y
  have hsmul : fderiv ℝ (c • extendGL φ) (y : Matrix n n ℝ)
      = c • fderiv ℝ (extendGL φ) (y : Matrix n n ℝ) :=
    ((((contDiffAt_extendGL hφ y).differentiableAt (by simp)).hasFDerivAt).const_smul c).fderiv
  rw [lieDerivFun_eq_fderiv (hφ.const_smul c), fderiv_extendGL_eq (hφ.const_smul c)
    (F := c • extendGL φ) (fun z => by simp [extendGL_coe hφ]) y, hsmul]
  simp [lieDerivFun_eq_fderiv hφ]

@[simp]
lemma lieDerivFun_zero_left (φ : GL n ℝ → ℂ) : lieDerivFun 0 φ = 0 := by
  funext y; simp [lieDerivFun]

lemma lieDerivFun_add_left {φ : GL n ℝ → ℂ} (hφ : IsSmoothOnGL φ) (X X' : Matrix n n ℝ) :
    lieDerivFun (X + X') φ = lieDerivFun X φ + lieDerivFun X' φ := by
  funext y
  simp [lieDerivFun_eq_fderiv hφ, mul_add]

lemma lieDerivFun_smul_left {φ : GL n ℝ → ℂ} (hφ : IsSmoothOnGL φ) (r : ℝ) (X : Matrix n n ℝ) :
    lieDerivFun (r • X) φ = r • lieDerivFun X φ := by
  funext y
  simp [lieDerivFun_eq_fderiv hφ]

lemma lieDerivFun_const (X : Matrix n n ℝ) (c : ℂ) :
    lieDerivFun X (fun _ : GL n ℝ => c) = 0 := by
  funext y
  simp [lieDerivFun]

/-- The left invariant derivative along `X` as a `ℂ`-linear endomorphism of the `C^∞`
functions on `GL n ℝ`. -/
noncomputable def lieDeriv (X : Matrix n n ℝ) : smoothGL n →ₗ[ℂ] smoothGL n where
  toFun φ := ⟨lieDerivFun X (φ : GL n ℝ → ℂ), φ.2.lieDerivFun X⟩
  map_add' φ ψ := Subtype.ext (by simpa using lieDerivFun_add φ.2 ψ.2 X)
  map_smul' c φ := Subtype.ext (by simpa using lieDerivFun_const_smul φ.2 c X)

@[simp]
lemma coe_lieDeriv (X : Matrix n n ℝ) (φ : smoothGL n) :
    (lieDeriv X φ : GL n ℝ → ℂ) = lieDerivFun X (φ : GL n ℝ → ℂ) := rfl

/-- The commutator of two left invariant derivatives is the left invariant derivative along the
commutator of the directions. This is the bracket identity that makes `lieDeriv` a Lie algebra
homomorphism; the second-order terms cancel by symmetry of the second derivative. -/
lemma lieDerivFun_bracket {φ : GL n ℝ → ℂ} (hφ : IsSmoothOnGL φ) (X Y : Matrix n n ℝ) :
    lieDerivFun (X * Y - Y * X) φ
      = lieDerivFun X (lieDerivFun Y φ) - lieDerivFun Y (lieDerivFun X φ) := by
  funext y
  have hY : fderiv ℝ (extendGL (lieDerivFun Y φ)) (y : Matrix n n ℝ)
      = fderiv ℝ (fun M => fderiv ℝ (extendGL φ) M (M * Y)) (y : Matrix n n ℝ) :=
    fderiv_extendGL_eq (hφ.lieDerivFun Y) (fun z => (lieDerivFun_eq_fderiv hφ Y z).symm) y
  have hX : fderiv ℝ (extendGL (lieDerivFun X φ)) (y : Matrix n n ℝ)
      = fderiv ℝ (fun M => fderiv ℝ (extendGL φ) M (M * X)) (y : Matrix n n ℝ) :=
    fderiv_extendGL_eq (hφ.lieDerivFun X) (fun z => (lieDerivFun_eq_fderiv hφ X z).symm) y
  rw [Pi.sub_apply, lieDerivFun_eq_fderiv hφ (X * Y - Y * X) y,
    lieDerivFun_eq_fderiv (hφ.lieDerivFun Y) X y, lieDerivFun_eq_fderiv (hφ.lieDerivFun X) Y y,
    hX, hY]
  exact (AutomorphicForm.LieDerivAux.fderiv_rightDeriv_sub_comm
    (contDiffAt_extendGL hφ y) X Y).symm

lemma lieDeriv_bracket (X Y : Matrix n n ℝ) :
    lieDeriv (X * Y - Y * X) = lieDeriv X * lieDeriv Y - lieDeriv Y * lieDeriv X := by
  refine LinearMap.ext fun φ => Subtype.ext ?_
  simpa using lieDerivFun_bracket φ.2 X Y

@[simp]
lemma lieDeriv_zero : lieDeriv (0 : Matrix n n ℝ) = 0 :=
  LinearMap.ext fun φ => Subtype.ext (by simp)

lemma lieDeriv_add (X X' : Matrix n n ℝ) : lieDeriv (X + X') = lieDeriv X + lieDeriv X' :=
  LinearMap.ext fun φ => Subtype.ext (by simpa using lieDerivFun_add_left φ.2 X X')

lemma lieDeriv_real_smul (r : ℝ) (X : Matrix n n ℝ) :
    lieDeriv (r • X) = (r : ℂ) • lieDeriv X :=
  LinearMap.ext fun φ => Subtype.ext (by simpa using lieDerivFun_smul_left φ.2 r X)

lemma lieDeriv_neg (X : Matrix n n ℝ) : lieDeriv (-X) = -lieDeriv X := by
  rw [show -X = (-1 : ℝ) • X by simp, lieDeriv_real_smul]
  push_cast
  module

lemma lieDeriv_sub (X X' : Matrix n n ℝ) : lieDeriv (X - X') = lieDeriv X - lieDeriv X' := by
  rw [sub_eq_add_neg, lieDeriv_add, lieDeriv_neg]
  abel

/-!
#### Complexification

`𝔤𝔩 n ℂ = 𝔤𝔩 n ℝ ⊗ ℂ` acts by `X + i Y ↦ lieDeriv X + i • lieDeriv Y`. Since the entrywise
real and imaginary parts turn complex matrix multiplication into the expected pair of real
products, the bracket identity over `ℝ` gives the bracket identity over `ℂ`.
-/

section
omit [Fintype n] [DecidableEq n]

lemma map_re_add (Z W : Matrix n n ℂ) :
    (Z + W).map Complex.re = Z.map Complex.re + W.map Complex.re :=
  Matrix.map_add _ Complex.add_re Z W

lemma map_im_add (Z W : Matrix n n ℂ) :
    (Z + W).map Complex.im = Z.map Complex.im + W.map Complex.im :=
  Matrix.map_add _ Complex.add_im Z W

lemma map_re_sub (Z W : Matrix n n ℂ) :
    (Z - W).map Complex.re = Z.map Complex.re - W.map Complex.re :=
  Matrix.map_sub _ Complex.sub_re Z W

lemma map_im_sub (Z W : Matrix n n ℂ) :
    (Z - W).map Complex.im = Z.map Complex.im - W.map Complex.im :=
  Matrix.map_sub _ Complex.sub_im Z W

lemma map_re_smul (c : ℂ) (Z : Matrix n n ℂ) :
    (c • Z).map Complex.re = c.re • Z.map Complex.re - c.im • Z.map Complex.im := by
  ext i j; simp [Complex.mul_re]

lemma map_im_smul (c : ℂ) (Z : Matrix n n ℂ) :
    (c • Z).map Complex.im = c.re • Z.map Complex.im + c.im • Z.map Complex.re := by
  ext i j; simp [Complex.mul_im]

end

section
omit [DecidableEq n]

lemma map_re_mul (Z W : Matrix n n ℂ) :
    (Z * W).map Complex.re
      = Z.map Complex.re * W.map Complex.re - Z.map Complex.im * W.map Complex.im := by
  ext i j
  simp [Matrix.mul_apply, Complex.mul_re, Finset.sum_sub_distrib]

lemma map_im_mul (Z W : Matrix n n ℂ) :
    (Z * W).map Complex.im
      = Z.map Complex.re * W.map Complex.im + Z.map Complex.im * W.map Complex.re := by
  ext i j
  simp [Matrix.mul_apply, Complex.mul_im, Finset.sum_add_distrib]

/-- The real part of a complex commutator, arranged as a difference of two real commutators. -/
lemma map_re_bracket (Z W : Matrix n n ℂ) :
    (Z * W - W * Z).map Complex.re
      = (Z.map Complex.re * W.map Complex.re - W.map Complex.re * Z.map Complex.re)
        - (Z.map Complex.im * W.map Complex.im - W.map Complex.im * Z.map Complex.im) := by
  rw [map_re_sub, map_re_mul, map_re_mul]
  abel

/-- The imaginary part of a complex commutator, arranged as a sum of two real commutators. -/
lemma map_im_bracket (Z W : Matrix n n ℂ) :
    (Z * W - W * Z).map Complex.im
      = (Z.map Complex.re * W.map Complex.im - W.map Complex.im * Z.map Complex.re)
        + (Z.map Complex.im * W.map Complex.re - W.map Complex.re * Z.map Complex.im) := by
  rw [map_im_sub, map_im_mul, map_im_mul]
  abel

end

/-- The action of the complexified Lie algebra `𝔤𝔩 n ℂ` of `GL n ℝ` on the `C^∞` functions:
`X + i Y` acts as `lieDeriv X + i • lieDeriv Y`. -/
noncomputable def lieDerivC (Z : Matrix n n ℂ) : Module.End ℂ (smoothGL n) :=
  lieDeriv (Z.map Complex.re) + Complex.I • lieDeriv (Z.map Complex.im)

lemma lieDerivC_add (Z W : Matrix n n ℂ) : lieDerivC (Z + W) = lieDerivC Z + lieDerivC W := by
  simp only [lieDerivC, map_re_add, map_im_add, lieDeriv_add, smul_add]
  abel

lemma lieDerivC_smul (c : ℂ) (Z : Matrix n n ℂ) : lieDerivC (c • Z) = c • lieDerivC Z := by
  have key : ∀ (a b : ℝ) (W : Matrix n n ℂ),
      lieDerivC (((a : ℂ) + (b : ℂ) * Complex.I) • W)
        = ((a : ℂ) + (b : ℂ) * Complex.I) • lieDerivC W := by
    intro a b W
    simp only [lieDerivC, map_re_smul, map_im_smul, lieDeriv_sub, lieDeriv_add,
      lieDeriv_real_smul, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    match_scalars
    all_goals ring_nf
    all_goals (try simp only [Complex.I_sq])
    all_goals ring
  simpa [Complex.re_add_im] using key c.re c.im Z

lemma lieDerivC_bracket (Z W : Matrix n n ℂ) :
    lieDerivC (Z * W - W * Z) = lieDerivC Z * lieDerivC W - lieDerivC W * lieDerivC Z := by
  -- The two commutators have to be assembled before `lieDeriv_sub` is allowed near them,
  -- or it splits `lieDeriv (A * C - C * A)` and the bracket identity no longer applies.
  simp only [lieDerivC]
  rw [map_re_bracket, map_im_bracket, lieDeriv_sub, lieDeriv_add]
  simp only [lieDeriv_bracket, mul_add, add_mul, smul_mul_assoc,
    mul_smul_comm, smul_smul, smul_add]
  match_scalars
  all_goals ring_nf
  all_goals (try simp only [Complex.I_sq])
  all_goals ring

end Smooth

end Matrix.GeneralLinearGroup
