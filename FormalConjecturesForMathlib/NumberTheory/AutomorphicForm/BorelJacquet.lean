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
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Instances.Matrix
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
* `integralAdeles` and `integralSubgroup`: the integral adeles `Ẑ` and the compact open
  subgroup `GL n Ẑ` of `G(𝔸_f)` witnessing condition (b1).
* `IsSmoothAdelic` and `IsAutomorphicForm`: smoothness on `G(𝔸)`, and the definition itself.
* `isAutomorphicForm_one`: the constant function `1` is an automorphic form — a sanity check
  exercising every condition; condition (c) holds through `constantsCharacter`, the character
  by which the centre acts on constants.
* `automorphicForms` and `rightTranslation`: the automorphic forms as a `ℂ`-submodule of the
  functions on `G(𝔸)`, with the right translation representation of `G(𝔸_f)` on it.

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

/-- `gnorm` is uniformly bounded below: since `y * y⁻¹ = 1`, the entries of `y` and `y⁻¹`
cannot all be small. This makes the exponent in a slow-increase bound enlargeable, hence
`IsSlowlyIncreasing` closed under addition. -/
lemma inv_card_le_gnorm (y : GL n ℝ) : (Fintype.card n : ℝ)⁻¹ ≤ gnorm y := by
  obtain ⟨i⟩ := ‹Nonempty n›
  have hcard : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hbound : (1 : ℝ) ≤ Fintype.card n * (gnorm y * gnorm y) := by
    have hy : ∑ k, (y : Matrix n n ℝ) i k * ((y⁻¹ : GL n ℝ) : Matrix n n ℝ) k i = 1 := by
      have h : ((y : Matrix n n ℝ) * ((y⁻¹ : GL n ℝ) : Matrix n n ℝ)) i i = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
      simpa [Matrix.mul_apply] using h
    calc (1 : ℝ)
        = |∑ k, (y : Matrix n n ℝ) i k * ((y⁻¹ : GL n ℝ) : Matrix n n ℝ) k i| := by
          rw [hy, abs_one]
      _ ≤ ∑ k, |(y : Matrix n n ℝ) i k * ((y⁻¹ : GL n ℝ) : Matrix n n ℝ) k i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : n, gnorm y * gnorm y := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]
          exact mul_le_mul ((le_entrySup _ i k).trans (le_max_left _ _))
            ((le_entrySup _ k i).trans (le_max_right _ _)) (abs_nonneg _) (gnorm_nonneg _)
      _ = Fintype.card n * (gnorm y * gnorm y) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  by_contra hcon
  replace hcon : gnorm y < (Fintype.card n : ℝ)⁻¹ := not_le.mp hcon
  have hc0 : (0 : ℝ) < Fintype.card n := zero_lt_one.trans_le hcard
  have h1 : Fintype.card n * (gnorm y * gnorm y)
      ≤ Fintype.card n * ((Fintype.card n : ℝ)⁻¹ * gnorm y) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcon.le (gnorm_nonneg y)) hc0.le
  have h2 : (Fintype.card n : ℝ) * ((Fintype.card n : ℝ)⁻¹ * gnorm y) = gnorm y := by
    field_simp
  have h3 : (Fintype.card n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hcard
  linarith [hbound.trans (h1.trans_eq h2)]

lemma gnorm_pos (y : GL n ℝ) : 0 < gnorm y :=
  ((inv_pos.mpr (by exact_mod_cast Fintype.card_pos)).trans_le (inv_card_le_gnorm y))

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

/-- A slow-increase bound with exponent `r` gives one with any exponent `r' ≥ r`: `gnorm` is
bounded below by `(Fintype.card n)⁻¹ > 0`, so the ratio `gnorm y ^ (r - r')` is bounded. -/
lemma exists_forall_norm_le_rpow_of_le {φ : GL n ℝ → ℂ} {C r : ℝ}
    (h : ∀ y, ‖φ y‖ ≤ C * gnorm y ^ r) {r' : ℝ} (hr : r ≤ r') :
    ∃ C', ∀ y, ‖φ y‖ ≤ C' * gnorm y ^ r' := by
  set c₀ : ℝ := (Fintype.card n : ℝ)⁻¹ with hc₀
  have hc₀0 : 0 < c₀ := inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hC0 : 0 ≤ C := by
    have h0 := (norm_nonneg (φ 1)).trans (h 1)
    exact (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos (gnorm_pos _) r)).mp h0
  refine ⟨C * (c₀ ^ (r' - r))⁻¹, fun y => ?_⟩
  have hkey : gnorm y ^ r ≤ (c₀ ^ (r' - r))⁻¹ * gnorm y ^ r' := by
    have hgpos := gnorm_pos y
    have hle : c₀ ^ (r' - r) ≤ gnorm y ^ (r' - r) :=
      Real.rpow_le_rpow hc₀0.le (inv_card_le_gnorm y) (sub_nonneg.mpr hr)
    have hsplit : gnorm y ^ r' = gnorm y ^ (r' - r) * gnorm y ^ r := by
      rw [← Real.rpow_add hgpos, sub_add_cancel]
    have hone : (1 : ℝ) ≤ (c₀ ^ (r' - r))⁻¹ * gnorm y ^ (r' - r) := by
      rw [← div_eq_inv_mul, le_div_iff₀ (Real.rpow_pos_of_pos hc₀0 _), one_mul]
      exact hle
    rw [hsplit, ← mul_assoc]
    exact le_mul_of_one_le_left (Real.rpow_nonneg hgpos.le r) hone
  calc ‖φ y‖ ≤ C * gnorm y ^ r := h y
    _ ≤ C * ((c₀ ^ (r' - r))⁻¹ * gnorm y ^ r') := mul_le_mul_of_nonneg_left hkey hC0
    _ = C * (c₀ ^ (r' - r))⁻¹ * gnorm y ^ r' := by ring

protected lemma IsSlowlyIncreasing.add {φ ψ : GL n ℝ → ℂ} (hφ : IsSlowlyIncreasing φ)
    (hψ : IsSlowlyIncreasing ψ) : IsSlowlyIncreasing (φ + ψ) := by
  obtain ⟨C₁, r₁, h₁⟩ := hφ
  obtain ⟨C₂, r₂, h₂⟩ := hψ
  obtain ⟨C₁', h₁'⟩ := exists_forall_norm_le_rpow_of_le h₁ (le_max_left r₁ r₂)
  obtain ⟨C₂', h₂'⟩ := exists_forall_norm_le_rpow_of_le h₂ (le_max_right r₁ r₂)
  refine ⟨C₁' + C₂', max r₁ r₂, fun y => ?_⟩
  calc ‖(φ + ψ) y‖ ≤ ‖φ y‖ + ‖ψ y‖ := norm_add_le _ _
    _ ≤ C₁' * gnorm y ^ max r₁ r₂ + C₂' * gnorm y ^ max r₁ r₂ := add_le_add (h₁' y) (h₂' y)
    _ = (C₁' + C₂') * gnorm y ^ max r₁ r₂ := (add_mul _ _ _).symm

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

omit [Nonempty n] in
instance : SMulCommClass ↥(centerUniversalEnveloping n) ℂ (smoothGL n) where
  smul_comm z c φ := by rw [centerAction_smul, centerAction_smul, map_smul]

omit [Nonempty n] in
instance : IsScalarTower ℂ ↥(centerUniversalEnveloping n) (smoothGL n) where
  smul_assoc c z φ := by
    rw [centerAction_smul, centerAction_smul, map_smul, LinearMap.smul_apply]

/-!
#### Constant functions are `Z(𝔤)`-finite

Left invariant derivatives kill constants, so the enveloping algebra maps the line of constant
functions to itself, through the character `constantsCharacter`; its kernel is an ideal of
finite codimension annihilating the constants.
-/

omit [Nonempty n] in
lemma lieDerivFun_const (X : Matrix n n ℝ) (c : ℂ) :
    lieDerivFun X (fun _ : GL n ℝ => c) = 0 := by
  funext y
  simp [lieDerivFun]

variable (n) in
omit [Nonempty n] in
/-- The constant function `1` as an element of `smoothGL n`; the constant functions are the
line it spans. -/
def oneSmoothGL : smoothGL n := ⟨fun _ => 1, isSmoothOnGL_const 1⟩

omit [Nonempty n] in
/-- An element of the line of constant functions is determined by its value at `1`. -/
lemma eq_smul_oneSmoothGL_of_mem_span {φ : smoothGL n} (hφ : φ ∈ (ℂ ∙ oneSmoothGL n)) :
    φ = (φ : GL n ℝ → ℂ) 1 • oneSmoothGL n := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hφ
  congr 1
  simp [oneSmoothGL]

omit [Nonempty n] in
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

omit [Nonempty n] in
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

/-- `K`-finiteness is closed under addition: the translate span of `f + g` sits inside the sum
of the translate spans. -/
protected lemma IsKFinite.add {f g : G → k} (hf : IsKFinite K k f) (hg : IsKFinite K k g) :
    IsKFinite K k (f + g) := by
  have hle : rightTranslateSpan K k (f + g)
      ≤ rightTranslateSpan K k f ⊔ rightTranslateSpan K k g := by
    rw [rightTranslateSpan, Submodule.span_le]
    rintro _ ⟨u, rfl⟩
    exact add_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨u, rfl⟩))
      (Submodule.mem_sup_right (Submodule.subset_span ⟨u, rfl⟩))
  have : FiniteDimensional k (rightTranslateSpan K k f) := hf
  have : FiniteDimensional k (rightTranslateSpan K k g) := hg
  exact Submodule.finiteDimensional_of_le hle

protected lemma IsKFinite.const_smul {f : G → k} (hf : IsKFinite K k f) (c : k) :
    IsKFinite K k (c • f) := by
  have hle : rightTranslateSpan K k (c • f) ≤ rightTranslateSpan K k f := by
    rw [rightTranslateSpan, Submodule.span_le]
    rintro _ ⟨u, rfl⟩
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨u, rfl⟩)
  have : FiniteDimensional k (rightTranslateSpan K k f) := hf
  exact Submodule.finiteDimensional_of_le hle

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

variable {k Z}

lemma isZFinite_zero : IsZFinite k Z (0 : M) := by
  refine ⟨⊤, ?_, fun z _ => smul_zero z⟩
  have : Subsingleton (Z ⧸ (⊤ : Ideal Z)) := Submodule.Quotient.subsingleton_iff.mpr rfl
  infer_instance

/-- `Z`-finiteness is closed under addition: the intersection of the two annihilating ideals
works, since `Z ⧸ (I ⊓ J)` embeds in `(Z ⧸ I) × (Z ⧸ J)`. -/
protected lemma IsZFinite.add {m₁ m₂ : M} (h₁ : IsZFinite k Z m₁) (h₂ : IsZFinite k Z m₂) :
    IsZFinite k Z (m₁ + m₂) := by
  obtain ⟨I, hI, hIann⟩ := h₁
  obtain ⟨J, hJ, hJann⟩ := h₂
  refine ⟨I ⊓ J, ?_, fun z hz => by rw [smul_add, hIann z hz.1, hJann z hz.2, add_zero]⟩
  have := hI; have := hJ
  have hker : I ⊓ J ≤ LinearMap.ker (LinearMap.prod I.mkQ J.mkQ) := by
    rw [LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]
  refine FiniteDimensional.of_injective
    (LinearMap.restrictScalars k ((I ⊓ J).liftQ (LinearMap.prod I.mkQ J.mkQ) hker)) ?_
  rw [LinearMap.coe_restrictScalars, ← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _
    (le_of_eq (by rw [LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]))

/-- `Z`-finiteness is preserved by scalar multiplication: the same ideal works. -/
protected lemma IsZFinite.const_smul [Module k M] [IsScalarTower k Z M] {m : M}
    (h : IsZFinite k Z m) (c : k) : IsZFinite k Z (c • m) := by
  obtain ⟨I, hI, hann⟩ := h
  refine ⟨I, hI, fun z hz => ?_⟩
  rw [← algebraMap_smul Z c m, smul_smul, mul_comm, ← smul_smul, hann z hz, smul_zero]

/-- An element on which `Z` acts through a `k`-algebra character is `Z`-finite: the kernel of
the character is an ideal of finite codimension annihilating it. -/
lemma IsZFinite.of_forall_smul_eq_algHom_smul [Module k M] (χ : Z →ₐ[k] k) {m : M}
    (h : ∀ z, z • m = χ z • m) : IsZFinite k Z m := by
  refine ⟨RingHom.ker χ, ?_, fun z hz => by rw [h z, RingHom.mem_ker.mp hz, zero_smul]⟩
  exact FiniteDimensional.of_injective (Ideal.kerLiftAlg χ).toLinearMap
    (Ideal.kerLiftAlg_injective χ)

/-- A constant family with `Z`-finite value is `Z`-finite, with the same ideal. -/
protected lemma IsZFinite.pi_const {ι : Type*} {m₀ : M} (h : IsZFinite k Z m₀) :
    IsZFinite k Z (fun _ : ι => m₀) := by
  obtain ⟨I, hI, hann⟩ := h
  refine ⟨I, hI, fun z hz => funext fun _ => ?_⟩
  simpa using hann z hz

/-- Precomposition preserves `Z`-finiteness of a family, with the same ideal. -/
protected lemma IsZFinite.comp {ι' ι : Type*} {m : ι → M} (h : IsZFinite k Z m) (σ : ι' → ι) :
    IsZFinite k Z (m ∘ σ) := by
  obtain ⟨I, hI, hann⟩ := h
  refine ⟨I, hI, fun z hz => funext fun x => ?_⟩
  simpa using congrFun (hann z hz) (σ x)

end ZFinite

end AutomorphicForm

namespace Matrix.GeneralLinearGroup

open AutomorphicForm

open scoped IsDedekindDomain.FiniteAdeleRing

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The constant function `1` is `Z(𝔤)`-finite: the kernel of `constantsCharacter` is an ideal
of finite codimension annihilating it. -/
lemma isZFinite_oneSmoothGL :
    IsZFinite ℂ ↥(centerUniversalEnveloping n) (oneSmoothGL n) :=
  IsZFinite.of_forall_smul_eq_algHom_smul (constantsCharacter n) fun z =>
    eq_smul_oneSmoothGL_of_mem_span (smul_oneSmoothGL_mem_span z)

/-- Every constant function is `Z(𝔤)`-finite. -/
lemma isZFinite_const_smoothGL (c : ℂ) :
    IsZFinite ℂ ↥(centerUniversalEnveloping n)
      (⟨fun _ => c, isSmoothOnGL_const c⟩ : smoothGL n) := by
  have h : (⟨fun _ => c, isSmoothOnGL_const c⟩ : smoothGL n) = c • oneSmoothGL n :=
    Subtype.ext (by funext y; simp [oneSmoothGL])
  rw [h]
  exact isZFinite_oneSmoothGL.const_smul c

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

section IntegralSubgroup

open IsDedekindDomain RestrictedProduct

set_option backward.isDefEq.respectTransparency false in
/-- The `v`-adic integers of `ℚ` are compact: they are homeomorphic to `ℤ_[p]` for the
corresponding prime `p`. -/
instance (v : HeightOneSpectrum ℤ) : CompactSpace (v.adicCompletionIntegers ℚ) := by
  have : Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  let _ : Algebra ℤ ↥(v.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  exact (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv
    v).toHomeomorph.symm.compactSpace

instance : T2Space 𝔸ᶠ[ℤ, ℚ] :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum ℤ,
    [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]))

/-- The integral adeles `Ẑ = ∏ᵥ ℤᵥ` as a subring of the finite adeles of `ℚ`: the adeles that
are integral at every place. -/
def integralAdeles : Subring 𝔸ᶠ[ℤ, ℚ] where
  carrier := {x | ∀ v, x v ∈ v.adicCompletionIntegers ℚ}
  one_mem' _v := one_mem _
  mul_mem' hx hy v := mul_mem (hx v) (hy v)
  zero_mem' _v := zero_mem _
  add_mem' hx hy v := add_mem (hx v) (hy v)
  neg_mem' hx v := neg_mem (hx v)

lemma isOpen_integralAdeles : IsOpen (integralAdeles : Set 𝔸ᶠ[ℤ, ℚ]) :=
  RestrictedProduct.isOpen_forall_mem fun _ => Valued.isOpen_valuationSubring _

lemma isCompact_integralAdeles : IsCompact (integralAdeles : Set 𝔸ᶠ[ℤ, ℚ]) := by
  have h : (integralAdeles : Set 𝔸ᶠ[ℤ, ℚ])
      = Set.range (structureMap (fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
          (fun v => v.adicCompletionIntegers ℚ) Filter.cofinite) := by
    rw [range_structureMap]
    rfl
  rw [h, ← Set.image_univ]
  exact (CompactSpace.isCompact_univ
    (X := Π v : HeightOneSpectrum ℤ, v.adicCompletionIntegers ℚ)).image
    isEmbedding_structureMap.continuous

variable (n) in
/-- `GL n Ẑ` inside `GL n 𝔸ᶠ[ℤ, ℚ]`: the matrices whose entries, and whose inverse's entries,
are integral adeles. It is a compact open subgroup of `G(𝔸_f)`
(`isOpen_integralSubgroup`, `isCompact_integralSubgroup`), as condition (b1) requires. -/
def integralSubgroup : Subgroup (GL n 𝔸ᶠ[ℤ, ℚ]) where
  carrier := {g | (∀ i j, (g : Matrix n n 𝔸ᶠ[ℤ, ℚ]) i j ∈ integralAdeles) ∧
      ∀ i j, (↑g⁻¹ : Matrix n n 𝔸ᶠ[ℤ, ℚ]) i j ∈ integralAdeles}
  one_mem' := by
    have h1 : ∀ i j : n, (1 : Matrix n n 𝔸ᶠ[ℤ, ℚ]) i j ∈ integralAdeles := fun i j => by
      rcases eq_or_ne i j with rfl | h
      · rw [Matrix.one_apply_eq]; exact one_mem _
      · rw [Matrix.one_apply_ne h]; exact zero_mem _
    exact ⟨fun i j => by simpa using h1 i j, fun i j => by simpa using h1 i j⟩
  mul_mem' {a b} ha hb := by
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [Units.val_mul, Matrix.mul_apply]
      exact Subring.sum_mem _ fun k _ => mul_mem (ha.1 i k) (hb.1 k j)
    · have hrev : ((a * b)⁻¹ : GL n 𝔸ᶠ[ℤ, ℚ]) = b⁻¹ * a⁻¹ := _root_.mul_inv_rev a b
      rw [hrev, Units.val_mul, Matrix.mul_apply]
      exact Subring.sum_mem _ fun k _ => mul_mem (hb.2 i k) (ha.2 k j)
  inv_mem' {a} ha := ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

lemma isOpen_integralSubgroup : IsOpen ((integralSubgroup n) : Set (GL n 𝔸ᶠ[ℤ, ℚ])) := by
  have hW : IsOpen {M : Matrix n n 𝔸ᶠ[ℤ, ℚ] | ∀ i j, M i j ∈ integralAdeles} := by
    have h : {M : Matrix n n 𝔸ᶠ[ℤ, ℚ] | ∀ i j, M i j ∈ integralAdeles}
        = ⋂ i, ⋂ j, (fun M : Matrix n n 𝔸ᶠ[ℤ, ℚ] => M i j) ⁻¹' integralAdeles := by
      ext M; simp
    rw [h]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_integralAdeles.preimage (continuous_id.matrix_elem i j)
  exact (hW.preimage Units.continuous_val).inter (hW.preimage Units.continuous_coe_inv)

lemma isCompact_integralSubgroup : IsCompact ((integralSubgroup n) : Set (GL n 𝔸ᶠ[ℤ, ℚ])) := by
  set W : Set (Matrix n n 𝔸ᶠ[ℤ, ℚ]) := {M | ∀ i j, M i j ∈ integralAdeles} with hWdef
  have hWc : IsCompact W := by
    have := isCompact_iff_compactSpace.mp isCompact_integralAdeles
    have hrange : Set.range (fun f : n → n → (integralAdeles : Set 𝔸ᶠ[ℤ, ℚ]) =>
        Matrix.of fun i j => (f i j : 𝔸ᶠ[ℤ, ℚ])) = W := by
      ext M
      constructor
      · rintro ⟨f, rfl⟩ i j
        exact (f i j).2
      · intro hM
        exact ⟨fun i j => ⟨M i j, hM i j⟩, rfl⟩
    rw [← hrange]
    refine isCompact_range (continuous_matrix fun i j => ?_)
    simp only [Matrix.of_apply]
    exact ((_root_.continuous_apply j).comp (_root_.continuous_apply i)).subtype_val
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  have himg : Units.embedProduct _ '' (integralSubgroup n)
      = (fun p : Matrix n n 𝔸ᶠ[ℤ, ℚ] × Matrix n n 𝔸ᶠ[ℤ, ℚ] => (p.1, MulOpposite.op p.2)) ''
        ((W ×ˢ W) ∩ {p | p.1 * p.2 = 1} ∩ {p | p.2 * p.1 = 1}) := by
    ext p
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨((g : Matrix n n 𝔸ᶠ[ℤ, ℚ]), ((g⁻¹ : GL n 𝔸ᶠ[ℤ, ℚ]) : Matrix n n 𝔸ᶠ[ℤ, ℚ])),
        ⟨⟨⟨hg.1, hg.2⟩, ?_⟩, ?_⟩, rfl⟩
      · rw [Set.mem_ofPred_eq, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      · rw [Set.mem_ofPred_eq, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    · rintro ⟨⟨A, B⟩, ⟨⟨⟨hA, hB⟩, h1⟩, h2⟩, rfl⟩
      exact ⟨⟨A, B, h1, h2⟩, ⟨hA, hB⟩, rfl⟩
  rw [himg]
  refine IsCompact.image ?_ (continuous_fst.prodMk (MulOpposite.continuous_op.comp continuous_snd))
  exact ((hWc.prod hWc).inter_right (isClosed_eq (continuous_fst.mul continuous_snd)
    continuous_const)).inter_right (isClosed_eq (continuous_snd.mul continuous_fst)
    continuous_const)

end IntegralSubgroup

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

/-! ### The submodule of automorphic forms and the right translation action -/

omit [Nonempty n] in
lemma isSmoothAdelic_const (c : ℂ) :
    IsSmoothAdelic (fun _ : GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ => c) where
  continuous := continuous_const
  locallyConstant _ := IsLocallyConstant.const c
  smoothOnGL _ := isSmoothOnGL_const c

omit [Nonempty n] in
protected lemma IsSmoothAdelic.add {f g : GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ → ℂ}
    (hf : IsSmoothAdelic f) (hg : IsSmoothAdelic g) : IsSmoothAdelic (f + g) where
  continuous := hf.continuous.add hg.continuous
  locallyConstant y := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [(hf.locallyConstant y).eventually_eq x,
      (hg.locallyConstant y).eventually_eq x] with z h1 h2
    simp [h1, h2]
  smoothOnGL x := (hf.smoothOnGL x).add (hg.smoothOnGL x)

omit [Nonempty n] in
protected lemma IsSmoothAdelic.const_smul {f : GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ → ℂ}
    (hf : IsSmoothAdelic f) (c : ℂ) : IsSmoothAdelic (c • f) where
  continuous := hf.continuous.const_smul c
  locallyConstant y := (hf.locallyConstant y).comp (c • ·)
  smoothOnGL x := (hf.smoothOnGL x).const_smul c

variable (n) in
/-- Sanity check: the constant functions are automorphic forms. This exercises every condition
of the definition: condition (b1) is witnessed by the compact open subgroup
`integralSubgroup n` and condition (c) by the kernel of `constantsCharacter n`. -/
theorem isAutomorphicForm_const (c : ℂ) :
    IsAutomorphicForm (fun _ : GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ => c) where
  smooth := isSmoothAdelic_const c
  left_invariant _ _ _ := rfl
  right_invariant := ⟨integralSubgroup n, isOpen_integralSubgroup, isCompact_integralSubgroup,
    fun _ _ _ => rfl⟩
  kFinite := isKFinite_of_rightInvariant fun _ _ => rfl
  zFinite := (isZFinite_const_smoothGL c).pi_const
  slowlyIncreasing _ := isSlowlyIncreasing_const c

variable (n) in
/-- Sanity check: the constant function `1` is an automorphic form. -/
theorem isAutomorphicForm_one :
    IsAutomorphicForm (fun _ : GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ => (1 : ℂ)) :=
  isAutomorphicForm_const n 1

protected lemma IsAutomorphicForm.add {f g : GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ → ℂ}
    (hf : IsAutomorphicForm f) (hg : IsAutomorphicForm g) : IsAutomorphicForm (f + g) where
  smooth := hf.smooth.add hg.smooth
  left_invariant γ hγ x := by
    simp [hf.left_invariant γ hγ x, hg.left_invariant γ hγ x]
  right_invariant := by
    obtain ⟨U₁, hU₁o, hU₁c, hU₁⟩ := hf.right_invariant
    obtain ⟨U₂, hU₂o, hU₂c, hU₂⟩ := hg.right_invariant
    refine ⟨U₁ ⊓ U₂, ?_, ?_, fun u hu x => ?_⟩
    · rw [Subgroup.coe_inf]
      exact hU₁o.inter hU₂o
    · rw [Subgroup.coe_inf]
      exact hU₁c.inter_right (U₂.isClosed_of_isOpen hU₂o)
    · have hu' := Subgroup.mem_inf.mp hu
      simp [hU₁ u hu'.1 x, hU₂ u hu'.2 x]
  kFinite := hf.kFinite.add hg.kFinite
  zFinite := hf.zFinite.add hg.zFinite
  slowlyIncreasing x := (hf.slowlyIncreasing x).add (hg.slowlyIncreasing x)

protected lemma IsAutomorphicForm.const_smul {f : GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ → ℂ}
    (hf : IsAutomorphicForm f) (c : ℂ) : IsAutomorphicForm (c • f) where
  smooth := hf.smooth.const_smul c
  left_invariant γ hγ x := by simp [hf.left_invariant γ hγ x]
  right_invariant := by
    obtain ⟨U, ho, hc', hU⟩ := hf.right_invariant
    exact ⟨U, ho, hc', fun u hu x => by simp [hU u hu x]⟩
  kFinite := hf.kFinite.const_smul c
  zFinite := hf.zFinite.const_smul c
  slowlyIncreasing x := (hf.slowlyIncreasing x).const_mul c

variable (n) in
/-- The automorphic forms for `GL n / ℚ` as a `ℂ`-submodule of the functions on `G(𝔸)`. -/
def automorphicForms : Submodule ℂ (GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ → ℂ) where
  carrier := {f | IsAutomorphicForm f}
  add_mem' hf hg := hf.add hg
  zero_mem' := isAutomorphicForm_const n 0
  smul_mem' c _ hf := hf.const_smul c

@[simp]
lemma mem_automorphicForms {f : GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ → ℂ} :
    f ∈ automorphicForms n ↔ IsAutomorphicForm f := Iff.rfl

/-- Automorphy is preserved by right translation in the finite variable. -/
protected lemma IsAutomorphicForm.rightTranslate {f : GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ → ℂ}
    (hf : IsAutomorphicForm f) (g : GL n 𝔸ᶠ[ℤ, ℚ]) :
    IsAutomorphicForm (fun p => f (p.1 * g, p.2)) where
  smooth :=
    { continuous := hf.smooth.continuous.comp
        ((continuous_fst.mul continuous_const).prodMk continuous_snd)
      locallyConstant := fun y => (hf.smooth.locallyConstant y).comp_continuous
        (continuous_mul_const g)
      smoothOnGL := fun x => hf.smooth.smoothOnGL (x * g) }
  left_invariant γ hγ x := by
    simpa [Prod.mul_def, mul_assoc] using hf.left_invariant γ hγ (x.1 * g, x.2)
  right_invariant := by
    obtain ⟨U, ho, hc', hU⟩ := hf.right_invariant
    have hset : (Subgroup.map (MulAut.conj g).toMonoidHom U : Set (GL n 𝔸ᶠ[ℤ, ℚ]))
        = (fun x => g * x * g⁻¹) '' U := by
      rw [Subgroup.coe_map]
      rfl
    refine ⟨Subgroup.map (MulAut.conj g).toMonoidHom U, ?_, ?_, ?_⟩
    · rw [hset]
      exact ((Homeomorph.mulRight g⁻¹).isOpenMap.comp (Homeomorph.mulLeft g).isOpenMap) _ ho
    · rw [hset]
      exact hc'.image ((continuous_const_mul g).mul continuous_const)
    · rintro u hu x
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hu
      simpa [MulAut.conj_apply, mul_assoc] using hU w hw (x.1 * g, x.2)
  kFinite := by
    set K := ((⊥ : Subgroup (GL n 𝔸ᶠ[ℤ, ℚ])).prod (orthogonalSubgroup n)) with hK
    set T : (GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ → ℂ) →ₗ[ℂ] (GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ → ℂ) :=
      { toFun := fun h => fun p => h (p.1 * g, p.2)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl } with hT
    have hle : rightTranslateSpan K ℂ (fun p => f (p.1 * g, p.2))
        ≤ Submodule.map T (rightTranslateSpan K ℂ f) := by
      rw [rightTranslateSpan, Submodule.span_le]
      rintro _ ⟨u, rfl⟩
      have hu1 : (u : GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ).1 = 1 :=
        Subgroup.mem_bot.mp (Subgroup.mem_prod.mp u.2).1
      refine Submodule.mem_map.mpr ⟨fun x => f (x * (u : GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ)),
        Submodule.subset_span ⟨u, rfl⟩, ?_⟩
      funext p
      simp [hT, hu1, Prod.mul_def]
    have h1 : FiniteDimensional ℂ (rightTranslateSpan K ℂ f) := hf.kFinite
    have h2 := Module.Finite.map (rightTranslateSpan K ℂ f) T
    exact Submodule.finiteDimensional_of_le hle
  zFinite := hf.zFinite.comp (· * g)
  slowlyIncreasing x := hf.slowlyIncreasing (x * g)

variable (n) in
/-- The right translation representation of `G(𝔸_f)` on the automorphic forms:
`g` acts by `f ↦ fun (x, y) => f (x * g, y)`. -/
noncomputable def rightTranslation :
    GL n 𝔸ᶠ[ℤ, ℚ] →* (automorphicForms n →ₗ[ℂ] automorphicForms n) where
  toFun g :=
    { toFun := fun f => ⟨fun p => (f : GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ → ℂ) (p.1 * g, p.2),
        f.2.rightTranslate g⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  map_one' := LinearMap.ext fun f => Subtype.ext (funext fun p => by simp)
  map_mul' g h := LinearMap.ext fun f => Subtype.ext (funext fun p => by
    simp [mul_assoc])

end Matrix.GeneralLinearGroup
