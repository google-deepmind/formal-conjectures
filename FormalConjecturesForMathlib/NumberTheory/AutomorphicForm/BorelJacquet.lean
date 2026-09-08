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

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

/-!
# Automorphic forms in the sense of Borel-Jacquet

Borel and Jacquet's definition (Corvallis) of an automorphic form, formalised for
`G = GL n / ℚ` with maximal compact subgroup `K = O n ℝ`, in the shape Buzzard states it for
`GL₂`. Writing `G(𝔸) = G(𝔸_f) × G(ℝ)`, where `G(𝔸_f) = GL n 𝔸ᶠ[ℤ, ℚ]` is the points of
`GL n` in the finite adeles of `ℚ`, an automorphic form is a smooth `f : G(𝔸) → ℂ` such that

* (a) `f (γ x) = f x` for all `γ ∈ G(ℚ)`, embedded diagonally;
* (b1) `f (x u) = f x` for all `u` in some compact open subgroup of `G(𝔸_f)`;
* (b2) the `ℂ`-span of the right translates `x ↦ f (x k)`, for `k ∈ K`, is
  finite-dimensional;
* (c) `f` is annihilated by an ideal of finite codimension of the centre of the universal
  enveloping algebra of the complexified Lie algebra of `G(ℝ)`, acting by left invariant
  differential operators;
* (d) for each `x ∈ G(𝔸_f)`, the function `y ↦ f (x, y)` on `G(ℝ)` is slowly increasing.

Smooth means continuous, locally constant in the finite variable and `C^∞` in the archimedean
one. The further condition (e) cutting out cusp forms, that the constant term along every
unipotent radical vanishes, is not formalised here: it needs Haar integration over
`N(ℚ) \ N(𝔸)`.

## Main declarations

All in the namespace `Matrix.GeneralLinearGroup` unless qualified otherwise, listed in the
order the file builds them:

* `AutomorphicForm.LieDerivAux.fderiv_rightDeriv_apply` and `…_sub_comm`: the product rule and
  bracket identity for the operator `F ↦ fun M => fderiv ℝ F M (M * X)` over an abstract
  normed algebra — the analytic core of condition (c).
* `gnorm` and `IsSlowlyIncreasing`: the norm `‖y‖ = max (|y|, |y⁻¹|)` on `GL n ℝ` and
  condition (d), slow increase.
* `IsSmoothOnGL` and `smoothGL`: the `C^∞` functions on `GL n ℝ`, as a predicate and as a
  `ℂ`-submodule.
* `lieDeriv`, `lieDerivC`, `envelopingAction`, `centerAction`: the actions on `smoothGL n` of
  `𝔤𝔩 n ℝ`, of its complexification, of `universalEnveloping n = U(𝔤𝔩 n ℂ)`, and of its
  centre `centerUniversalEnveloping n` — the action of condition (c).
* `AutomorphicForm.IsKFinite` and `AutomorphicForm.IsZFinite`: the finiteness conditions (b2)
  and (c), for an abstract group and module respectively.
* `ratDiagonal` and `orthogonalSubgroup`: the diagonal copy of `GL n ℚ` in `G(𝔸_f) × G(ℝ)`
  (condition (a)) and the orthogonal group `K = O n ℝ` (condition (b2)).
* `IsSmoothAdelic` and `IsAutomorphicForm`: smoothness on `G(𝔸)`, and the definition itself.

## Relation to the literature

Buzzard states (b2) through a finite-dimensional representation `σ` of `K`; for compact `K`
that formulation is equivalent to the one used here, since the span of the translates is a
continuous, hence semisimple, finite-dimensional representation of `K`. Conditions (b1) and
(b2) together are the `K`-finiteness of Getz-Hahn's Definition 6.5 for `K = K_∞ K^∞` with
`K^∞ ≤ G(𝔸_f)` compact open.

Condition (d) follows Buzzard in letting the constants depend on the finite variable.
Getz-Hahn's Definition 6.4 instead imposes one global bound `|f g| ≤ c * H g ^ r` for their
adelic height `H`; for `GL n` that height factors as `H (x, y) = H_f x * gnorm y`, so the
global bound implies (d). Only these implications are asserted; no equivalence with
Getz-Hahn's full definition is claimed.

## Implementation notes

Smoothness on `GL n ℝ` is phrased as the existence of a `C^∞` extension to the open set of
invertible matrices (`IsSmoothOnGL`), rather than through a manifold structure: the normed
ring instances on `Matrix n n ℝ` that would give `GL n ℝ` a chart are scoped, and conflict
with the product topology that `GL n ℝ` already carries.

The action of condition (c) is constructed, not assumed. `X ∈ 𝔤𝔩 n ℝ` acts by differentiating
along the one-parameter subgroup, `(X • φ) y = d/dt φ (y * exp (t • X)) |_{t = 0}`; this
equals `fderiv ℝ F y (y * X)` for any `C^∞` extension `F` of `φ` (`lieDerivFun_eq_fderiv`),
through which every algebraic property is proved. The bracket identity is the product rule
plus symmetry of the second derivative; complexifying and applying
`UniversalEnvelopingAlgebra.lift` gives `centerAction`. The action lives on `smoothGL n`, not
on all of `G(𝔸) → ℂ` — a differential operator has nothing to act on at a non-differentiable
function — so condition (c) asks for one ideal annihilating every slice `y ↦ f (x, y)` at
once, the finite variable being a spectator.

The product rule is proved over an abstract finite-dimensional normed `ℝ`-algebra and
instantiated at `Matrix n n ℝ`. That is forced: Mathlib's norms on `Matrix n n ℝ` are scoped
instances while its topology is global, so instance search cannot assemble
`SeminormedAddCommGroup (Matrix n n ℝ →L[ℝ] ℂ)` for the written-out type even though the
instance term typechecks, and the second-derivative lemmas behind the product rule need that
instance as an argument. Instantiating an abstract lemma supplies its instance arguments
instead of searching for them.

Compactness of `orthogonalSubgroup n` and its maximality (Cartan-Iwasawa-Malcev, which also
makes it unique up to conjugacy) are asserted in its docstring but not formalised; of
compactness, the boundedness half is proved (`abs_coe_le_one_of_mem_orthogonalSubgroup`).

*References:*
 - A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*, in Automorphic
   forms, representations and L-functions (Corvallis), Proc. Sympos. Pure Math. 33 (1979), §4
 - [K. Buzzard, *Automorphic forms for GL2 over
   Q*](https://www.ma.imperial.ac.uk/~buzzard/maths/research/notes/automorphic_forms_for_gl2_over_Q.pdf),
   §1
 - [J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*, GTM 300
   (2024)](https://sites.duke.edu/jgetz/files/2022/04/Graduate_Text.pdf), §6.2 and §6.3;
   in the numbering of that text, Definitions 6.1 (moderate growth), 6.2 (`Z(𝔤)`-finiteness),
   6.4 (adelic moderate growth) and 6.5 (adelic automorphic form)
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

variable {n : Type*} [Fintype n] [Nonempty n]

/-! ### Slow increase: condition (d) -/

/-- The sup norm on the entries of a matrix: for `n = 2` this is
`|(a b; c d)| = max {|a|, |b|, |c|, |d|}`. -/
noncomputable def entrySup (M : Matrix n n ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i =>
    Finset.univ.sup' Finset.univ_nonempty fun j => |M i j|

lemma le_entrySup (M : Matrix n n ℝ) (i j : n) : |M i j| ≤ entrySup M :=
  le_trans (Finset.le_sup' (fun j => |M i j|) (Finset.mem_univ j))
    (Finset.le_sup' (fun i => Finset.univ.sup' Finset.univ_nonempty fun j => |M i j|)
      (Finset.mem_univ i))

lemma entrySup_nonneg (M : Matrix n n ℝ) : 0 ≤ entrySup M :=
  le_trans (abs_nonneg _) (le_entrySup M (Classical.arbitrary n) (Classical.arbitrary n))

variable [DecidableEq n]

/-- The norm `‖y‖ = max (|y|, |y⁻¹|)` on `GL n ℝ`, with `|·|` the sup norm on matrix entries.
This is the norm used to define slow increase.

For `G = GL n` this is exactly the archimedean factor of the norm Getz-Hahn use for a general
reductive `G`: theirs is the sup of the entries of `ι y`, for `ι : G → SL (2 * n)` the embedding
`y ↦ (y, (y⁻¹)ᵗ)`, whose entries are those of `y` together with those of `y⁻¹`. -/
noncomputable def gnorm (y : GL n ℝ) : ℝ :=
  max (entrySup (y : Matrix n n ℝ)) (entrySup ((y⁻¹ : GL n ℝ) : Matrix n n ℝ))

lemma gnorm_nonneg (y : GL n ℝ) : 0 ≤ gnorm y :=
  le_max_of_le_left (entrySup_nonneg _)

@[simp]
lemma gnorm_inv (y : GL n ℝ) : gnorm y⁻¹ = gnorm y := by
  rw [gnorm, gnorm, inv_inv, max_comm]

/-- A function `φ : GL n ℝ → ℂ` is *slowly increasing*, or of *moderate growth*, if
`‖φ y‖ ≤ C * ‖y‖ ^ r` for some `C` and `r`. This is condition (d) in the definition of an
automorphic form. -/
def IsSlowlyIncreasing (φ : GL n ℝ → ℂ) : Prop :=
  ∃ C r : ℝ, ∀ y : GL n ℝ, ‖φ y‖ ≤ C * gnorm y ^ r

lemma IsSlowlyIncreasing.of_bounded {φ : GL n ℝ → ℂ} {C : ℝ} (h : ∀ y, ‖φ y‖ ≤ C) :
    IsSlowlyIncreasing φ :=
  ⟨C, 0, fun y => by simpa using h y⟩

lemma isSlowlyIncreasing_const (c : ℂ) : IsSlowlyIncreasing (fun _ : GL n ℝ => c) :=
  IsSlowlyIncreasing.of_bounded fun _ => le_rfl

lemma IsSlowlyIncreasing.const_mul {φ : GL n ℝ → ℂ} (hφ : IsSlowlyIncreasing φ) (c : ℂ) :
    IsSlowlyIncreasing fun y => c * φ y := by
  obtain ⟨C, r, hC⟩ := hφ
  refine ⟨‖c‖ * C, r, fun y => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg c)

/-! ### Smooth functions on `GL n ℝ` -/

section Smooth

omit [Nonempty n]
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

omit [Fintype n] [DecidableEq n] in
lemma map_re_add (Z W : Matrix n n ℂ) :
    (Z + W).map Complex.re = Z.map Complex.re + W.map Complex.re := by
  ext i j; simp

omit [Fintype n] [DecidableEq n] in
lemma map_im_add (Z W : Matrix n n ℂ) :
    (Z + W).map Complex.im = Z.map Complex.im + W.map Complex.im := by
  ext i j; simp

omit [Fintype n] [DecidableEq n] in
lemma map_re_smul (c : ℂ) (Z : Matrix n n ℂ) :
    (c • Z).map Complex.re = c.re • Z.map Complex.re - c.im • Z.map Complex.im := by
  ext i j; simp [Complex.mul_re]

omit [Fintype n] [DecidableEq n] in
lemma map_im_smul (c : ℂ) (Z : Matrix n n ℂ) :
    (c • Z).map Complex.im = c.re • Z.map Complex.im + c.im • Z.map Complex.re := by
  ext i j; simp [Complex.mul_im]

omit [DecidableEq n] in
lemma map_re_mul (Z W : Matrix n n ℂ) :
    (Z * W).map Complex.re
      = Z.map Complex.re * W.map Complex.re - Z.map Complex.im * W.map Complex.im := by
  ext i j
  simp [Matrix.mul_apply, Complex.mul_re, Finset.sum_sub_distrib]

omit [DecidableEq n] in
lemma map_im_mul (Z W : Matrix n n ℂ) :
    (Z * W).map Complex.im
      = Z.map Complex.re * W.map Complex.im + Z.map Complex.im * W.map Complex.re := by
  ext i j
  simp [Matrix.mul_apply, Complex.mul_im, Finset.sum_add_distrib]

omit [Fintype n] [DecidableEq n] in
lemma map_re_sub (Z W : Matrix n n ℂ) :
    (Z - W).map Complex.re = Z.map Complex.re - W.map Complex.re := by
  ext i j; simp

omit [Fintype n] [DecidableEq n] in
lemma map_im_sub (Z W : Matrix n n ℂ) :
    (Z - W).map Complex.im = Z.map Complex.im - W.map Complex.im := by
  ext i j; simp

omit [DecidableEq n] in
/-- The real part of a complex commutator, arranged as a difference of two real commutators. -/
lemma map_re_bracket (Z W : Matrix n n ℂ) :
    (Z * W - W * Z).map Complex.re
      = (Z.map Complex.re * W.map Complex.re - W.map Complex.re * Z.map Complex.re)
        - (Z.map Complex.im * W.map Complex.im - W.map Complex.im * Z.map Complex.im) := by
  rw [map_re_sub, map_re_mul, map_re_mul]
  abel

omit [DecidableEq n] in
/-- The imaginary part of a complex commutator, arranged as a sum of two real commutators. -/
lemma map_im_bracket (Z W : Matrix n n ℂ) :
    (Z * W - W * Z).map Complex.im
      = (Z.map Complex.re * W.map Complex.im - W.map Complex.im * Z.map Complex.re)
        + (Z.map Complex.im * W.map Complex.re - W.map Complex.re * Z.map Complex.im) := by
  rw [map_im_sub, map_im_mul, map_im_mul]
  abel

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

/-! ### The enveloping algebra, its centre, and their action: condition (c) -/

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

omit [Nonempty n] in
lemma centerAction_smul (z : ↥(centerUniversalEnveloping n)) (φ : smoothGL n) :
    z • φ = centerAction z φ := rfl

end Matrix.GeneralLinearGroup

namespace AutomorphicForm

/-! ### The finiteness conditions (b2) and (c), abstractly -/

section KFinite

variable {G : Type*} [Group G] (K : Subgroup G) (k : Type*) [Field k] (f : G → k)

/-- The `k`-span of the right translates of `f` by the subgroup `K`. -/
def rightTranslateSpan : Submodule k (G → k) :=
  Submodule.span k (Set.range fun u : K => fun x => f (x * (u : G)))

lemma self_mem_rightTranslateSpan : f ∈ rightTranslateSpan K k f :=
  Submodule.subset_span ⟨1, funext fun x => by simp⟩

/-- `f` is `K`-finite: the span of its right `K`-translates is finite-dimensional. This is
condition (b2) in the definition of an automorphic form. -/
def IsKFinite : Prop := FiniteDimensional k (rightTranslateSpan K k f)

variable {K k f}

/-- A function invariant under right translation by `K` is `K`-finite. -/
lemma isKFinite_of_rightInvariant (h : ∀ (x : G) (u : K), f (x * (u : G)) = f x) :
    IsKFinite K k f := by
  have hsub : (Set.range fun u : K => fun x => f (x * (u : G))) ⊆ {f} := by
    rintro _ ⟨u, rfl⟩
    exact funext fun x => h x u
  exact FiniteDimensional.span_of_finite k ((Set.finite_singleton f).subset hsub)

/-- If `K` is finite then every function is `K`-finite. -/
lemma isKFinite_of_finite [Finite K] : IsKFinite K k f :=
  FiniteDimensional.span_of_finite k (Set.finite_range _)

end KFinite

section ZFinite

variable (k : Type*) [Field k] (Z : Type*) [CommRing Z] [Algebra k Z]
  {M : Type*} [AddCommGroup M] [Module Z M]

/-- `m` is *`Z`-finite*: it is annihilated by an ideal of `Z` of finite codimension over `k`.
This is condition (c), with `Z` the centre of the universal enveloping algebra of the
complexified Lie algebra of `G(ℝ)`, i.e.
`Matrix.GeneralLinearGroup.centerUniversalEnveloping n`.

This is Getz-Hahn's Definition 6.2, in the form they state for a vector of an arbitrary
`Z(𝔤)`-module. They note it is equivalent to `Z • m` being finite-dimensional over `k`. -/
def IsZFinite (m : M) : Prop :=
  ∃ I : Ideal Z, FiniteDimensional k (Z ⧸ I) ∧ ∀ z ∈ I, z • m = 0

end ZFinite

end AutomorphicForm

namespace Matrix.GeneralLinearGroup

open AutomorphicForm

open scoped IsDedekindDomain.FiniteAdeleRing

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The subgroups `Γ = G(ℚ)` and `K = O n ℝ`: conditions (a) and (b2) -/

variable (n) in
/-- The diagonal embedding of the rational points `G(ℚ) = GL n ℚ` into
`G(𝔸_f) × G(ℝ) = GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ`, through the inclusions of `ℚ` into the finite
adeles and into `ℝ`. -/
noncomputable def diagonalEmbedding : GL n ℚ →* GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ :=
  (map (algebraMap ℚ 𝔸ᶠ[ℤ, ℚ])).prod (map (algebraMap ℚ ℝ))

variable (n) in
/-- The subgroup `Γ = G(ℚ)` of `G(𝔸_f) × G(ℝ)`: the range of the diagonal embedding of
`GL n ℚ`. Condition (a) for an automorphic form is left invariance under this subgroup. -/
noncomputable def ratDiagonal : Subgroup (GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ) :=
  (diagonalEmbedding n).range

/-- The orthogonal group `O n ℝ` as a subgroup of `GL n ℝ`: the matrices whose transpose is
their inverse. This is the maximal compact subgroup of `GL n ℝ` — up to conjugacy the only one,
by the Cartan-Iwasawa-Malcev theorem — and it is the `K` of the pair `(G, K)` in the definition
of an automorphic form for `GL n`. -/
def orthogonalSubgroup (n : Type*) [Fintype n] [DecidableEq n] : Subgroup (GL n ℝ) where
  carrier := {y | (y : Matrix n n ℝ)ᵀ = (↑y⁻¹ : Matrix n n ℝ)}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [Units.val_mul, Matrix.transpose_mul, ha, hb]
    simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [inv_inv, ← ha, Matrix.transpose_transpose]

@[simp]
lemma mem_orthogonalSubgroup {y : GL n ℝ} :
    y ∈ orthogonalSubgroup n ↔ (y : Matrix n n ℝ)ᵀ = (↑y⁻¹ : Matrix n n ℝ) := Iff.rfl

lemma mem_orthogonalSubgroup_iff_mul_transpose {y : GL n ℝ} :
    y ∈ orthogonalSubgroup n ↔ (y : Matrix n n ℝ) * (y : Matrix n n ℝ)ᵀ = 1 := by
  rw [mem_orthogonalSubgroup]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h]; exact y.mul_inv
  · rw [← Matrix.inv_eq_right_inv h, Matrix.GeneralLinearGroup.coe_inv]

/-- The entries of an orthogonal matrix are bounded by `1`: each row is a unit vector. This is
the boundedness half of the compactness of `orthogonalSubgroup n`; see the implementation notes
on what is and is not formalised about that. -/
lemma abs_coe_le_one_of_mem_orthogonalSubgroup {y : GL n ℝ} (hy : y ∈ orthogonalSubgroup n)
    (i j : n) : |(y : Matrix n n ℝ) i j| ≤ 1 := by
  set M := (y : Matrix n n ℝ) with hM
  have h : M * Mᵀ = 1 := mem_orthogonalSubgroup_iff_mul_transpose.mp hy
  have hd : ∑ k, M i k * M i k = 1 := by
    have := congrArg (fun A => A i i) h
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hle : M i j * M i j ≤ ∑ k, M i k * M i k :=
    Finset.single_le_sum (f := fun k => M i k * M i k) (fun k _ => mul_self_nonneg _)
      (Finset.mem_univ j)
  rw [hd] at hle
  nlinarith [abs_nonneg (M i j), sq_abs (M i j)]

variable [Nonempty n]

/-! ### The definition -/

/-- Smoothness of a function on `G(𝔸) = G(𝔸_f) × G(ℝ)`, with `G(𝔸_f) = GL n 𝔸ᶠ[ℤ, ℚ]`:
continuous, locally constant in the finite variable, and `C^∞` in the archimedean variable. -/
structure IsSmoothAdelic (f : GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ → ℂ) : Prop where
  continuous : Continuous f
  locallyConstant : ∀ y : GL n ℝ, IsLocallyConstant fun x : GL n 𝔸ᶠ[ℤ, ℚ] => f (x, y)
  smoothOnGL : ∀ x : GL n 𝔸ᶠ[ℤ, ℚ], IsSmoothOnGL fun y : GL n ℝ => f (x, y)

/-- An automorphic form for `(G, K)` in the sense of Borel-Jacquet, with
`G = GL n / ℚ` and `K = O n ℝ`: `G(𝔸)` is written as
`G(𝔸_f) × G(ℝ) = GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ`, condition (a) is invariance under `ratDiagonal n`,
the rational points embedded diagonally, condition (b2) is finiteness under the maximal compact
`orthogonalSubgroup n`, and condition (c) is with respect to the action of the centre of the
universal enveloping algebra by left invariant differential operators, `centerAction`. -/
structure IsAutomorphicForm (f : GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ → ℂ) : Prop where
  /-- `f` is smooth. -/
  smooth : IsSmoothAdelic f
  /-- (a) `f (γ x) = f x` for `γ ∈ G(ℚ)`. -/
  left_invariant : ∀ γ ∈ ratDiagonal n, ∀ x, f (γ * x) = f x
  /-- (b1) `f` is right invariant under some compact open subgroup of `G(𝔸_f)`. -/
  right_invariant : ∃ U : Subgroup (GL n 𝔸ᶠ[ℤ, ℚ]), IsOpen (U : Set (GL n 𝔸ᶠ[ℤ, ℚ])) ∧
    IsCompact (U : Set (GL n 𝔸ᶠ[ℤ, ℚ])) ∧
    ∀ u ∈ U, ∀ x : GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ, f (x.1 * u, x.2) = f x
  /-- (b2) `f` is `K`-finite. -/
  kFinite : IsKFinite ((⊥ : Subgroup (GL n 𝔸ᶠ[ℤ, ℚ])).prod (orthogonalSubgroup n)) ℂ f
  /-- (c) `f` is annihilated by an ideal of finite codimension of the centre of the universal
  enveloping algebra, acting in the archimedean variable. One ideal annihilates every
  finite-adelic slice at once. -/
  zFinite : IsZFinite ℂ ↥(centerUniversalEnveloping n)
    (fun x : GL n 𝔸ᶠ[ℤ, ℚ] => (⟨fun y => f (x, y), smooth.smoothOnGL x⟩ : smoothGL n))
  /-- (d) `y ↦ f (x, y)` is slowly increasing for each `x ∈ G(𝔸_f)`. -/
  slowlyIncreasing : ∀ x : GL n 𝔸ᶠ[ℤ, ℚ], IsSlowlyIncreasing fun y => f (x, y)

end Matrix.GeneralLinearGroup
