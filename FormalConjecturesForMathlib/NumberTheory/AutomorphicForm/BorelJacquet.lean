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

public import FormalConjecturesForMathlib.NumberTheory.AutomorphicForm.BorelJacquet.CenterAction
public import FormalConjecturesForMathlib.NumberTheory.AutomorphicForm.BorelJacquet.LieDeriv
public import FormalConjecturesForMathlib.NumberTheory.AutomorphicForm.BorelJacquet.Subgroups
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.OpenSubgroup
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

All in the namespace `Matrix.GeneralLinearGroup` unless qualified otherwise:

* `AutomorphicForm.IsKFinite` and `AutomorphicForm.IsZFinite`: the finiteness conditions (b2)
  and (c), for an abstract group and module respectively.
* `gnorm` and `IsSlowlyIncreasing`: the norm `‖y‖ = max (|y|, |y⁻¹|)` on `GL n ℝ` and
  condition (d), slow increase.
* `IsSmoothAdelic` and `IsAutomorphicForm`: smoothness on `G(𝔸)`, and the definition itself.
* `isAutomorphicForm_one`: the constant function `1` is an automorphic form — a sanity check
  exercising every condition; condition (c) holds through `constantsCharacter`, the character
  by which the centre acts on constants.
* `automorphicForms` and `rightTranslation`: the automorphic forms as a `ℂ`-submodule of the
  functions on `G(𝔸)`, with the right translation representation of `G(𝔸_f)` on it.

The remaining ingredients of the definition are developed in the `BorelJacquet` subdirectory:

* `BorelJacquet.LieDeriv`: the `C^∞` functions on `GL n ℝ` (`IsSmoothOnGL`, `smoothGL`) and
  the action on them of `𝔤𝔩 n ℝ` and its complexification (`lieDeriv`, `lieDerivC`).
* `BorelJacquet.CenterAction`: the enveloping algebra `universalEnveloping`, its centre
  `centerUniversalEnveloping`, their action (`envelopingAction`, `centerAction`) — the action
  of condition (c) — and the character `constantsCharacter`.
* `BorelJacquet.Subgroups`: the subgroups `ratDiagonal` (condition (a)), `orthogonalSubgroup`
  (condition (b2)) and `integralSubgroup` (the compact open subgroup witnessing condition
  (b1)).

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

The action of condition (c) is constructed, not assumed; see
`FormalConjecturesForMathlib.NumberTheory.AutomorphicForm.BorelJacquet.LieDeriv` and
`FormalConjecturesForMathlib.NumberTheory.AutomorphicForm.BorelJacquet.CenterAction` for the
construction. The action lives on `smoothGL n`, not on all of `G(𝔸) → ℂ` — a differential
operator has nothing to act on at a non-differentiable function — so condition (c) asks for
one ideal annihilating every slice `y ↦ f (x, y)` at once, the finite variable being a
spectator.

*References:*
 - A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*, in Automorphic
   forms, representations and L-functions (Corvallis), Proc. Sympos. Pure Math. 33 (1979), §4
 - K. Buzzard, *Automorphic forms for GL2 over Q*, §1.
   https://www.ma.imperial.ac.uk/~buzzard/maths/research/notes/automorphic_forms_for_gl2_over_Q.pdf
 - J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*, GTM 300 (2024),
   §6.2 and §6.3; in the numbering of that text, Definitions 6.1 (moderate growth),
   6.2 (`Z(𝔤)`-finiteness), 6.4 (adelic moderate growth) and 6.5 (adelic automorphic form).
   https://sites.duke.edu/jgetz/files/2022/04/Graduate_Text.pdf
-/

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
    IsKFinite K k f :=
  FiniteDimensional.span_of_finite k <| (Set.finite_singleton f).subset <|
    Set.range_subset_iff.mpr fun u => funext fun x => h x u

/-- If `K` is finite then every function is `K`-finite. -/
lemma isKFinite_of_finite [Finite K] : IsKFinite K k f :=
  FiniteDimensional.span_of_finite k (Set.finite_range _)

/-- `K`-finiteness is closed under addition: the translate span of `f + g` sits inside the sum
of the translate spans. -/
protected lemma IsKFinite.add {f g : G → k} (hf : IsKFinite K k f) (hg : IsKFinite K k g) :
    IsKFinite K k (f + g) :=
  haveI : FiniteDimensional k (rightTranslateSpan K k f) := hf
  haveI : FiniteDimensional k (rightTranslateSpan K k g) := hg
  Submodule.finiteDimensional_of_le
    (S₂ := rightTranslateSpan K k f ⊔ rightTranslateSpan K k g) <|
    Submodule.span_le.mpr <| Set.range_subset_iff.mpr fun u =>
      add_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨u, rfl⟩))
        (Submodule.mem_sup_right (Submodule.subset_span ⟨u, rfl⟩))

protected lemma IsKFinite.const_smul {f : G → k} (hf : IsKFinite K k f) (c : k) :
    IsKFinite K k (c • f) :=
  haveI : FiniteDimensional k (rightTranslateSpan K k f) := hf
  Submodule.finiteDimensional_of_le (S₂ := rightTranslateSpan K k f) <| Submodule.span_le.mpr <|
    Set.range_subset_iff.mpr fun u => Submodule.smul_mem _ c (Submodule.subset_span ⟨u, rfl⟩)

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

lemma isZFinite_zero : IsZFinite k Z (0 : M) := ⟨⊤, inferInstance, fun z _ => smul_zero z⟩

/-- `Z`-finiteness is closed under addition: the intersection of the two annihilating ideals
works, since `Z ⧸ (I ⊓ J)` embeds in `(Z ⧸ I) × (Z ⧸ J)`. -/
protected lemma IsZFinite.add {m₁ m₂ : M} (h₁ : IsZFinite k Z m₁) (h₂ : IsZFinite k Z m₂) :
    IsZFinite k Z (m₁ + m₂) := by
  obtain ⟨I, hI, hIann⟩ := h₁; obtain ⟨J, hJ, hJann⟩ := h₂
  have hker : LinearMap.ker (I.mkQ.prod J.mkQ) = I ⊓ J := by simp [LinearMap.ker_prod]
  refine ⟨I ⊓ J, FiniteDimensional.of_injective (((I ⊓ J).liftQ (I.mkQ.prod J.mkQ)
    hker.ge).restrictScalars k) ?_, fun z hz => by simp [smul_add, hIann z hz.1, hJann z hz.2]⟩
  simpa [← LinearMap.ker_eq_bot] using Submodule.ker_liftQ_eq_bot _ _ _ hker.le

/-- `Z`-finiteness is preserved by scalar multiplication: the same ideal works. -/
protected lemma IsZFinite.const_smul [Module k M] [IsScalarTower k Z M] {m : M}
    (h : IsZFinite k Z m) (c : k) : IsZFinite k Z (c • m) :=
  h.imp fun _ => And.imp_right fun hann z hz => by
    rw [← algebraMap_smul Z c m, smul_smul, mul_comm, ← smul_smul, hann z hz, smul_zero]

/-- An element on which `Z` acts through a `k`-algebra character is `Z`-finite: the kernel of
the character is an ideal of finite codimension annihilating it. -/
lemma IsZFinite.of_forall_smul_eq_algHom_smul [Module k M] (χ : Z →ₐ[k] k) {m : M}
    (h : ∀ z, z • m = χ z • m) : IsZFinite k Z m :=
  ⟨RingHom.ker χ, FiniteDimensional.of_injective (Ideal.kerLiftAlg χ).toLinearMap
    (Ideal.kerLiftAlg_injective χ), fun z hz => by rw [h z, RingHom.mem_ker.mp hz, zero_smul]⟩

/-- A constant family with `Z`-finite value is `Z`-finite, with the same ideal. -/
protected lemma IsZFinite.pi_const {ι : Type*} {m₀ : M} (h : IsZFinite k Z m₀) :
    IsZFinite k Z (fun _ : ι => m₀) :=
  h.imp fun _ => And.imp_right fun hann z hz => funext fun _ => hann z hz

/-- Precomposition preserves `Z`-finiteness of a family, with the same ideal. -/
protected lemma IsZFinite.comp {ι' ι : Type*} {m : ι → M} (h : IsZFinite k Z m) (σ : ι' → ι) :
    IsZFinite k Z (m ∘ σ) :=
  h.imp fun _ => And.imp_right fun hann z hz => funext fun x => congrFun (hann z hz) (σ x)

end ZFinite

end AutomorphicForm

namespace Matrix.GeneralLinearGroup

open AutomorphicForm

open scoped IsDedekindDomain.FiniteAdeleRing

variable {n : Type*} [Fintype n] [Nonempty n]

/-! ### Slow increase: condition (d) -/

/-- The sup norm on the entries of a matrix: for `n = 2` this is
`|(a b; c d)| = max {|a|, |b|, |c|, |d|}`. -/
noncomputable def entrySup (M : Matrix n n ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i =>
    Finset.univ.sup' Finset.univ_nonempty fun j => |M i j|

lemma le_entrySup (M : Matrix n n ℝ) (i j : n) : |M i j| ≤ entrySup M :=
  Finset.le_sup'_of_le _ (Finset.mem_univ i) (Finset.le_sup' (|M i ·|) (Finset.mem_univ j))

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
  have hy : ∑ k, (y : Matrix n n ℝ) i k * ((y⁻¹ : GL n ℝ) : Matrix n n ℝ) k i = 1 := by
    simpa [Matrix.mul_apply, Matrix.one_apply_eq] using congrFun (congrFun y.mul_inv i) i
  have hk : ∀ k, |(y : Matrix n n ℝ) i k * ((y⁻¹ : GL n ℝ) : Matrix n n ℝ) k i|
      ≤ gnorm y * gnorm y := fun k => by
    rw [abs_mul]; exact mul_le_mul ((le_entrySup _ i k).trans (le_max_left _ _))
      ((le_entrySup _ k i).trans (le_max_right _ _)) (abs_nonneg _) (gnorm_nonneg _)
  have hbound : (1 : ℝ) ≤ Fintype.card n * (gnorm y * gnorm y) := by
    rw [← abs_one, ← hy]; refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum
      fun k _ => hk k).trans (le_of_eq ?_))
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [inv_le_iff_one_le_mul₀ (zero_lt_one.trans_le hcard)]; nlinarith [gnorm_nonneg y]

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
  have hC0 : 0 ≤ C := (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos (gnorm_pos _) r)).mp
    ((norm_nonneg (φ 1)).trans (h 1))
  have hg : ∀ y : GL n ℝ, gnorm y ^ (r - r') ≤ (Fintype.card n : ℝ)⁻¹ ^ (r - r') := fun y =>
    Real.rpow_le_rpow_of_nonpos (inv_pos.mpr (by exact_mod_cast Fintype.card_pos))
      (inv_card_le_gnorm y) (sub_nonpos.mpr hr)
  refine ⟨C * (Fintype.card n : ℝ)⁻¹ ^ (r - r'), fun y => ?_⟩
  calc ‖φ y‖ ≤ C * gnorm y ^ r := h y
    _ = C * (gnorm y ^ (r - r') * gnorm y ^ r') := by
        rw [← Real.rpow_add (gnorm_pos y), sub_add_cancel]
    _ ≤ C * ((Fintype.card n : ℝ)⁻¹ ^ (r - r') * gnorm y ^ r') := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hg y) (Real.rpow_nonneg (gnorm_pos y).le _)) hC0
    _ = C * (Fintype.card n : ℝ)⁻¹ ^ (r - r') * gnorm y ^ r' := (mul_assoc _ _ _).symm

protected lemma IsSlowlyIncreasing.add {φ ψ : GL n ℝ → ℂ} (hφ : IsSlowlyIncreasing φ)
    (hψ : IsSlowlyIncreasing ψ) : IsSlowlyIncreasing (φ + ψ) := by
  obtain ⟨C₁, r₁, h₁⟩ := hφ; obtain ⟨C₂, r₂, h₂⟩ := hψ
  obtain ⟨C₁', h₁'⟩ := exists_forall_norm_le_rpow_of_le h₁ (le_max_left r₁ r₂)
  obtain ⟨C₂', h₂'⟩ := exists_forall_norm_le_rpow_of_le h₂ (le_max_right r₁ r₂)
  exact ⟨C₁' + C₂', max r₁ r₂, fun y => ((norm_add_le _ _).trans
    (add_le_add (h₁' y) (h₂' y))).trans_eq (add_mul _ _ _).symm⟩

/-! ### Constant functions are `Z(𝔤)`-finite -/

omit [Nonempty n] in
/-- The constant function `1` is `Z(𝔤)`-finite: the kernel of `constantsCharacter` is an ideal
of finite codimension annihilating it. -/
lemma isZFinite_oneSmoothGL :
    IsZFinite ℂ ↥(centerUniversalEnveloping n) (oneSmoothGL n) :=
  IsZFinite.of_forall_smul_eq_algHom_smul (constantsCharacter n) fun z =>
    eq_smul_oneSmoothGL_of_mem_span (smul_oneSmoothGL_mem_span z)

omit [Nonempty n] in
/-- Every constant function is `Z(𝔤)`-finite. -/
lemma isZFinite_const_smoothGL (c : ℂ) :
    IsZFinite ℂ ↥(centerUniversalEnveloping n)
      (⟨fun _ => c, isSmoothOnGL_const c⟩ : smoothGL n) :=
  (Subtype.ext (funext fun _ => mul_one c) :
    c • oneSmoothGL n = ⟨fun _ => c, _⟩) ▸ isZFinite_oneSmoothGL.const_smul c

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
  locallyConstant y := (hf.locallyConstant y).add (hg.locallyConstant y)
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
    obtain ⟨⟨U₁, o₁, c₁, h₁⟩, U₂, o₂, c₂, h₂⟩ := And.intro hf.right_invariant hg.right_invariant
    exact ⟨U₁ ⊓ U₂, Subgroup.coe_inf U₁ U₂ ▸ o₁.inter o₂,
      Subgroup.coe_inf U₁ U₂ ▸ c₁.inter_right (U₂.isClosed_of_isOpen o₂),
      fun u hu x => by simp [h₁ u hu.1 x, h₂ u hu.2 x]⟩
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
    obtain ⟨U, ho, hc, hU⟩ := hf.right_invariant
    have hset : (Subgroup.map (MulAut.conj g).toMonoidHom U : Set (GL n 𝔸ᶠ[ℤ, ℚ]))
        = (fun x => g * x * g⁻¹) '' U := by rw [Subgroup.coe_map]; rfl
    refine ⟨_, hset ▸ ((Homeomorph.mulRight g⁻¹).isOpenMap.comp
      (Homeomorph.mulLeft g).isOpenMap) _ ho,
      hset ▸ hc.image ((continuous_const_mul g).mul continuous_const), fun u hu x => ?_⟩
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hu
    simpa [MulAut.conj_apply, mul_assoc] using hU w hw (x.1 * g, x.2)
  kFinite := by
    have : FiniteDimensional ℂ (rightTranslateSpan
      ((⊥ : Subgroup (GL n 𝔸ᶠ[ℤ, ℚ])).prod (orthogonalSubgroup n)) ℂ f) := hf.kFinite
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.map
      (LinearMap.funLeft ℂ ℂ fun p : GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ => (p.1 * g, p.2))
      (rightTranslateSpan ((⊥ : Subgroup (GL n 𝔸ᶠ[ℤ, ℚ])).prod (orthogonalSubgroup n)) ℂ f))
      (Submodule.span_le.mpr <| Set.range_subset_iff.mpr fun u => Submodule.mem_map.mpr
        ⟨_, Submodule.subset_span ⟨u, rfl⟩, funext fun p => by
          simp [Subgroup.mem_bot.mp (Subgroup.mem_prod.mp u.2).1, Prod.mul_def]⟩)
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
