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

public import FormalConjecturesForMathlib.NumberTheory.ModularForms.Hecke.CosetRepresentatives
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic

@[expose] public section

/-!
# Hecke operators `T_n` on level-one cusp forms

This file defines the classical Hecke operators `T_n` of weight `k` on `CuspForm 𝒮ℒ k`, the space
of cusp forms of level one (`𝒮ℒ` is the image of `SL(2, ℤ)` in `GL(2, ℝ)`), as `ℂ`-linear
endomorphisms. On functions `f : ℍ → ℂ` the operator is the explicit finite sum

`T_n f = ∑_{a d = n} ∑_{0 ≤ b < d} f ∣[k] !![a, b; 0, d]`,

where `∣[k]` is Mathlib's weight-`k` slash action of `GL(2, ℝ)`. Unfolding the slash action,

`(T_n f) τ = n ^ (k - 1) * ∑_{a d = n} ∑_{0 ≤ b < d} d ^ (-k) * f ((a * τ + b) / d)`,

which is the normalisation of Diamond–Shurman, Proposition 5.3.1: `T_p` acts on a normalised
eigenform with eigenvalue `a_p`, and on `q`-expansions
`a_m (T_n f) = ∑_{d ∣ gcd(m, n)} d ^ (k - 1) * a_{m n / d ^ 2} (f)`.

## Main definitions

* `ModularForm.heckeMatrix a b d`: the matrix `!![a, b; 0, d]` as an element of `GL (Fin 2) ℝ`.
* `ModularForm.heckeOperator k n f`: `T_n f` for a function `f : ℍ → ℂ`.
* `CuspForm.heckeOperator k n f`: `T_n f` for a cusp form `f`, as a cusp form.
* `CuspForm.heckeOperatorₗ k n`: `T_n` as a `ℂ`-linear endomorphism of `CuspForm 𝒮ℒ k`.

## Main results

* `ModularForm.heckeOperator_apply`: the explicit pointwise formula.
* `ModularForm.heckeOperator_add`, `ModularForm.heckeOperator_smul`: `ℂ`-linearity.
* `ModularForm.heckeOperator_eq_sum_heckeIndex`: the bridge to the index set of
  `CosetRepresentatives.lean`.
* `ModularForm.heckeOperator_slash_of_mem`: **modularity is preserved**, by the coset
  reduction of `CosetRepresentatives.lean`.
* `ModularForm.mdifferentiable_heckeOperator`: holomorphy is preserved.
* `ModularForm.isZeroAtImInfty_heckeOperator`: vanishing at `i∞` is preserved.
* `ModularForm.isZeroAt_heckeOperator`: the cusp condition at every cusp of `𝒮ℒ`, derived from
  modularity.
* `ModularForm.heckeOperator_one`, `ModularForm.heckeOperator_two`: checks in small index.

## The all-index convention

The sum defining `T_n` runs over *all* upper-triangular integer matrices of determinant `n`, up
to left multiplication by `SL(2, ℤ)`; these represent the right cosets of `SL(2, ℤ)` in the whole
set of integer matrices of determinant `n`, which is the union of the double cosets
`SL(2, ℤ) · diag(e, n / e) · SL(2, ℤ)` over `e ^ 2 ∣ n`. This is the classical `T_n` of
Diamond–Shurman, §5.3, and Serre, Chapter VII, §5. It differs from the slash operator of the single
double coset `SL(2, ℤ) · diag(1, n) · SL(2, ℤ)` — the primitive part `T(1, n)`, the sum over the
representatives with `gcd(a, b, d) = 1` — unless `n` is squarefree. For example
`T_4 = T(1, 4) + 2 ^ (k - 2)`, because the scalar matrix `2 • 1` acts on weight-`k` functions as
multiplication by `2 ^ (k - 2)`.

## Provenance

Adapted from the Tau Ceti library (<https://github.com/TauCetiProject/TauCeti>, commit
`15f5a24264f9f68db33e56530aad2d8d9faf7ac1`, Apache-2.0, The Tau Ceti contributors and
Chris Birkbeck): the modules `TauCeti/NumberTheory/ModularForms/HeckeSlash/Basic.lean`,
`HeckeSlash/UpperTri/Sum.lean`, `HeckeSlash/ModularForm.lean` and `HeckeSlash/Operators.lean`,
which build Hecke operators at level `Γ₁(N)` as slash operators of abstract double cosets and
bundle them as endomorphisms of Mathlib's `CuspForm`. Tau Ceti's construction in turn descends
from the AINTLIB `LeanModularForms` project (<https://github.com/CBirkbeck/AINTLIB>,
Chris Birkbeck, Apache-2.0). The operator here is instead defined by a concrete finite sum of
slashes, because the abstract Hecke-ring and double-coset development is a large dependency tree
that only the *proofs* need. At level one, Tau Ceti's operator is the primitive part `T(1, n)`
described above, of which the classical `T_n` is the sum over all double cosets of determinant
`n`. No proof code is transcribed.

## References

* F. Diamond and J. Shurman, *A first course in modular forms*, §5.2–5.3.
* G. Shimura, *Introduction to the arithmetic theory of automorphic functions*, §3.4–3.5.
* J.-P. Serre, *A course in arithmetic*, Chapter VII, §5.
-/

open UpperHalfPlane Matrix Finset

open scoped MatrixGroups ModularForm Manifold

namespace ModularForm

/-! ### The coset representatives `!![a, b; 0, d]` -/

section heckeMatrix

/-- The upper-triangular matrix `!![a, b; 0, d]` as an element of `GL (Fin 2) ℝ`. The matrices
with `a * d = n` and `0 ≤ b < d` represent the right cosets of `SL(2, ℤ)` in the set of integer
matrices of determinant `n`, and the Hecke operator `T_n` is the sum of the slashes by them.
When `a * d = 0` the matrix is singular and the junk value `1` is returned. -/
noncomputable def heckeMatrix (a b d : ℕ) : GL (Fin 2) ℝ :=
  if h : a * d = 0 then 1 else
    GeneralLinearGroup.mkOfDetNeZero !![(a : ℝ), b; 0, d]
      (by rw [det_fin_two_of, mul_zero, sub_zero]; exact_mod_cast h)

variable {a b d : ℕ}

/-- The junk branch: when `a d = 0` the matrix `!![a, b; 0, d]` is singular, and `heckeMatrix`
returns the identity. -/
lemma heckeMatrix_of_mul_eq_zero (h : a * d = 0) : heckeMatrix a b d = 1 := dif_pos h

/-- The underlying matrix of `heckeMatrix a b d`, away from the junk branch. -/
lemma coe_heckeMatrix (h : a * d ≠ 0) :
    (heckeMatrix a b d : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), b; 0, d] := by
  simp [heckeMatrix, h]

/-- The lower-left entry vanishes, in every case. This is the hypothesis under which Mathlib's
`IsBoundedAtImInfty.slash` and `IsZeroAtImInfty.slash` apply. -/
@[simp]
lemma heckeMatrix_apply_one_zero : heckeMatrix a b d 1 0 = 0 := by
  by_cases h : a * d = 0 <;> simp [heckeMatrix_of_mul_eq_zero, coe_heckeMatrix, h]

/-- `det !![a, b; 0, d] = a d`. The hypothesis is needed: on the junk branch the determinant
is `1`. -/
lemma det_heckeMatrix (h : a * d ≠ 0) :
    (heckeMatrix a b d : Matrix (Fin 2) (Fin 2) ℝ).det = a * d := by
  simp [coe_heckeMatrix h, det_fin_two_of]

/-- The representatives have positive determinant, so the slash action is untwisted. -/
lemma det_heckeMatrix_pos (h : a * d ≠ 0) :
    0 < (heckeMatrix a b d : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [det_heckeMatrix h]
  exact_mod_cast Nat.pos_of_ne_zero h

/-- The determinant is positive, so the slash action carries no complex-conjugation twist. -/
lemma σ_heckeMatrix (h : a * d ≠ 0) (z : ℂ) : σ (heckeMatrix a b d) z = z := by
  simp [σ, det_heckeMatrix_pos h]

/-- The automorphy denominator of `!![a, b; 0, d]` is the constant `d`, since the lower-left
entry vanishes. -/
lemma denom_heckeMatrix (h : a * d ≠ 0) (z : ℂ) : denom (heckeMatrix a b d) z = d := by
  simp [denom, coe_heckeMatrix h]

/-- The Möbius action of `!![a, b; 0, d]` on `ℍ` is `τ ↦ (a * τ + b) / d`. -/
lemma coe_heckeMatrix_smul (h : a * d ≠ 0) (τ : ℍ) :
    ((heckeMatrix a b d • τ : ℍ) : ℂ) = (a * τ + b) / d := by
  rw [coe_smul_of_det_pos (by simpa using det_heckeMatrix_pos h), num, denom_heckeMatrix h]
  simp [coe_heckeMatrix h]

/-- **Slashing by `!![a, b; 0, d]`**:
`(f ∣[k] !![a, b; 0, d]) τ = (a * d) ^ (k - 1) * d ^ (-k) * f ((a * τ + b) / d)`. -/
lemma slash_heckeMatrix_apply (h : a * d ≠ 0) (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] heckeMatrix a b d) τ =
      ((a * d : ℕ) : ℂ) ^ (k - 1) * (d : ℂ) ^ (-k) * f (heckeMatrix a b d • τ) := by
  have habs : |((heckeMatrix a b d).det : ℝ)| = ((a * d : ℕ) : ℝ) := by
    simp [det_heckeMatrix h, abs_mul]
  rw [slash_apply, σ_heckeMatrix h, denom_heckeMatrix h, habs, Complex.ofReal_natCast]
  ring

/-- `!![1, 0; 0, 1]` is the identity. -/
lemma heckeMatrix_one_zero_one : heckeMatrix 1 0 1 = 1 :=
  Units.ext <| by simp [coe_heckeMatrix, one_fin_two]

end heckeMatrix

/-! ### The operator on functions `ℍ → ℂ` -/

/-- **The classical Hecke operator `T_n`** of weight `k`, on functions `ℍ → ℂ`:
`T_n f = ∑_{a d = n} ∑_{0 ≤ b < d} f ∣[k] !![a, b; 0, d]`. For `n = 0` the sum is empty. -/
noncomputable def heckeOperator (k : ℤ) (n : ℕ) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ x ∈ n.divisorsAntidiagonal, ∑ b ∈ range x.2, f ∣[k] heckeMatrix x.1 b x.2

variable (k : ℤ) (n : ℕ)

private lemma mul_ne_zero_of_mem_divisorsAntidiagonal {x : ℕ × ℕ}
    (hx : x ∈ n.divisorsAntidiagonal) : x.1 * x.2 ≠ 0 :=
  mul_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx)
    (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx)

/-- **The explicit formula**:
`(T_n f) τ = ∑_{a d = n} ∑_{0 ≤ b < d} n ^ (k - 1) * d ^ (-k) * f ((a * τ + b) / d)`,
where `(a * τ + b) / d` is spelled as the Möbius image `heckeMatrix a b d • τ`
(`coe_heckeMatrix_smul`). -/
theorem heckeOperator_apply (f : ℍ → ℂ) (τ : ℍ) :
    heckeOperator k n f τ = ∑ x ∈ n.divisorsAntidiagonal, ∑ b ∈ range x.2,
      (n : ℂ) ^ (k - 1) * (x.2 : ℂ) ^ (-k) * f (heckeMatrix x.1 b x.2 • τ) := by
  simp only [heckeOperator, Finset.sum_apply]
  refine sum_congr rfl fun x hx ↦ sum_congr rfl fun b _ ↦ ?_
  rw [slash_heckeMatrix_apply (mul_ne_zero_of_mem_divisorsAntidiagonal n hx),
    (Nat.mem_divisorsAntidiagonal.mp hx).1]

/-- `T_n` kills the zero function. -/
@[simp]
theorem heckeOperator_zero : heckeOperator k n 0 = 0 := by
  simp [heckeOperator]

/-- `T_n` is additive. -/
@[simp]
theorem heckeOperator_add (f g : ℍ → ℂ) :
    heckeOperator k n (f + g) = heckeOperator k n f + heckeOperator k n g := by
  simp [heckeOperator, sum_add_distrib]

/-- **`T_n` is `ℂ`-homogeneous.** Since every representative has positive determinant, the
scalar passes through the slash action without a conjugation twist. -/
@[simp]
theorem heckeOperator_smul (c : ℂ) (f : ℍ → ℂ) :
    heckeOperator k n (c • f) = c • heckeOperator k n f := by
  simp only [heckeOperator, smul_sum]
  refine sum_congr rfl fun x hx ↦ sum_congr rfl fun b _ ↦ ?_
  rw [smul_slash, σ_heckeMatrix (mul_ne_zero_of_mem_divisorsAntidiagonal n hx)]

/-- `T_0 = 0`: the index set is empty because `divisorsAntidiagonal 0 = ∅`. -/
@[simp]
theorem heckeOperator_index_zero (f : ℍ → ℂ) : heckeOperator k 0 f = 0 := by
  simp [heckeOperator, Nat.divisorsAntidiagonal_zero]

/-- `T_1` is the identity. -/
@[simp]
theorem heckeOperator_one (f : ℍ → ℂ) : heckeOperator k 1 f = f := by
  simp [heckeOperator, Nat.divisorsAntidiagonal_one, heckeMatrix_one_zero_one]

/-- `T_n` as a single sum over the index set `heckeIndex n`. -/
lemma heckeOperator_eq_sum_heckeIndex (f : ℍ → ℂ) :
    heckeOperator k n f = ∑ p ∈ heckeIndex n, f ∣[k] heckeMatrix p.1.1 p.2 p.1.2 := by
  rw [heckeOperator, sum_heckeIndex]

/-- The matrix of `heckeMatrix a b d` is the integer matrix `heckeMatrixInt ((a, d), b)`. -/
lemma coe_heckeMatrix_eq_map {p : (ℕ × ℕ) × ℕ} (hp : p ∈ heckeIndex n) :
    (heckeMatrix p.1.1 p.2 p.1.2 : Matrix (Fin 2) (Fin 2) ℝ) =
      (heckeMatrixInt p).map (algebraMap ℤ ℝ) := by
  obtain ⟨hp, hn, -⟩ := mem_heckeIndex.mp hp
  rw [coe_heckeMatrix (hp ▸ hn), heckeMatrixInt]
  simp [← Matrix.ext_iff, Fin.forall_fin_two]

/-- Right multiplication by `γ ∈ SL(2, ℤ)` leaves the determinant of a representative unchanged,
so `heckeMatrixInt p * γ` still has positive determinant. -/
lemma det_heckeMatrixInt_mul_pos {p : (ℕ × ℕ) × ℕ} (hp : p ∈ heckeIndex n) (γ : SL(2, ℤ)) :
    0 < (heckeMatrixInt p * (γ : Matrix (Fin 2) (Fin 2) ℤ)).det := by
  rw [det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one]
  exact det_heckeMatrixInt_pos hp

/-- Right multiplication by `γ ∈ SL(2, ℤ)`, followed by Hermite reduction, maps the index set of
`T_n` into itself. -/
lemma hermiteReduce_heckeMatrixInt_mul_mem {p : (ℕ × ℕ) × ℕ} (hp : p ∈ heckeIndex n)
    (γ : SL(2, ℤ)) : hermiteReduce (heckeMatrixInt p * γ) ∈ heckeIndex n := by
  have := hermiteReduce_mem_heckeIndex (det_heckeMatrixInt_mul_pos n hp γ)
  rwa [det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one, det_heckeMatrixInt_of_mem hp,
    Int.toNat_natCast] at this

/-- The map `p ↦ hermiteReduce (heckeMatrixInt p * γ)` on the index set is inverted by the same
construction for `γ⁻¹`, so it is a permutation. -/
lemma hermiteReduce_heckeMatrixInt_mul_inv {p : (ℕ × ℕ) × ℕ} (hp : p ∈ heckeIndex n)
    (γ : SL(2, ℤ)) :
    hermiteReduce (heckeMatrixInt (hermiteReduce (heckeMatrixInt p * γ)) *
      (γ⁻¹ : SL(2, ℤ))) = p := by
  rw [← hermiteTransform_mul (det_heckeMatrixInt_mul_pos n hp γ), mul_assoc, mul_assoc,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
    mul_one, hermiteReduce_mul_left
      (det_hermiteTransform (det_heckeMatrixInt_mul_pos n hp γ).ne')
      (det_heckeMatrixInt_pos hp), hermiteReduce_heckeMatrixInt hp]

/-- **The coset-permutation identity.** On a `𝒮ℒ`-invariant function `f`, slashing by the
representative `!![a, b; 0, d]` and then by `γ ∈ SL(2, ℤ)` is slashing by the representative of
the coset of `!![a, b; 0, d] * γ`, since the two differ by an element of `SL(2, ℤ)` on the left
(`hermiteTransform_mul`). -/
lemma slash_heckeMatrix_slash_mapGL {f : ℍ → ℂ} (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f)
    {p : (ℕ × ℕ) × ℕ} (hp : p ∈ heckeIndex n) (γ : SL(2, ℤ)) :
    (f ∣[k] heckeMatrix p.1.1 p.2 p.1.2) ∣[k] SpecialLinearGroup.mapGL ℝ γ =
      f ∣[k] heckeMatrix (hermiteReduce (heckeMatrixInt p * γ)).1.1
        (hermiteReduce (heckeMatrixInt p * γ)).2 (hermiteReduce (heckeMatrixInt p * γ)).1.2 := by
  set A := heckeMatrixInt p * (γ : Matrix (Fin 2) (Fin 2) ℤ)
  have hA : 0 < A.det := det_heckeMatrixInt_mul_pos n hp γ
  have hmem : hermiteReduce A ∈ heckeIndex n := hermiteReduce_heckeMatrixInt_mul_mem n hp γ
  have hdet : (adjugate (hermiteTransform A)).det = 1 := by
    rw [det_adjugate, det_hermiteTransform hA.ne', one_pow]
  -- the element of `SL(2, ℤ)` connecting `!![a, b; 0, d] * γ` to the reduced representative
  let δ : SL(2, ℤ) := ⟨adjugate (hermiteTransform A), hdet⟩
  have key : heckeMatrix p.1.1 p.2 p.1.2 * SpecialLinearGroup.mapGL ℝ γ =
      SpecialLinearGroup.mapGL ℝ δ * heckeMatrix (hermiteReduce A).1.1 (hermiteReduce A).2
        (hermiteReduce A).1.2 := by
    apply Units.ext
    simp only [GeneralLinearGroup.coe_mul, coe_heckeMatrix_eq_map n hp,
      coe_heckeMatrix_eq_map n hmem, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, ← Matrix.map_mul]
    congr 1
    exact eq_adjugate_hermiteTransform_mul hA
  rw [← SlashAction.slash_mul, key, SlashAction.slash_mul, hf _ ⟨δ, rfl⟩]

/-- **`T_n` preserves modularity**: if `f` is slash-invariant under `𝒮ℒ`, so is `T_n f`.

Right multiplication by `γ ∈ SL(2, ℤ)` permutes the right cosets `SL(2, ℤ) · !![a, b; 0, d]`
(`a * d = n`, `0 ≤ b < d`) of the set of integer matrices of determinant `n`
(Diamond–Shurman, Proposition 5.2.1 and §5.3; Shimura, Proposition 3.37). The permutation is
`p ↦ hermiteReduce (heckeMatrixInt p * γ)`, with inverse given by `γ⁻¹`. -/
theorem heckeOperator_slash_of_mem {f : ℍ → ℂ} (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f)
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ 𝒮ℒ) :
    heckeOperator k n f ∣[k] γ = heckeOperator k n f := by
  obtain ⟨γ, rfl⟩ := hγ
  rw [heckeOperator_eq_sum_heckeIndex, SlashAction.sum_slash]
  refine sum_nbij' (fun p ↦ hermiteReduce (heckeMatrixInt p * γ))
    (fun p ↦ hermiteReduce (heckeMatrixInt p * (γ⁻¹ : SL(2, ℤ))))
    (fun p hp ↦ hermiteReduce_heckeMatrixInt_mul_mem n hp γ)
    (fun p hp ↦ hermiteReduce_heckeMatrixInt_mul_mem n hp γ⁻¹)
    (fun p hp ↦ hermiteReduce_heckeMatrixInt_mul_inv n hp γ)
    (fun p hp ↦ by simpa using hermiteReduce_heckeMatrixInt_mul_inv n hp γ⁻¹)
    (fun p hp ↦ slash_heckeMatrix_slash_mapGL k n hf hp γ)

/-- `T_n` preserves holomorphy. -/
theorem mdifferentiable_heckeOperator {f : ℍ → ℂ} (hf : MDiff f) :
    MDiff (heckeOperator k n f) :=
  MDifferentiable.sum fun _ _ ↦ MDifferentiable.sum fun _ _ ↦ hf.slash k _

/-- `T_n` preserves vanishing at `i∞`, since each representative is upper triangular. -/
theorem isZeroAtImInfty_heckeOperator {f : ℍ → ℂ} (hf : IsZeroAtImInfty f) :
    IsZeroAtImInfty (heckeOperator k n f) :=
  Submodule.sum_mem (Filter.zeroAtFilterSubmodule ℂ atImInfty) fun _ _ ↦
    Submodule.sum_mem _ fun _ _ ↦ hf.slash k heckeMatrix_apply_one_zero

/-- `T_n f` vanishes at every cusp of `𝒮ℒ` when `f` is modular and vanishes at `i∞`. -/
theorem isZeroAt_heckeOperator {f : ℍ → ℂ} (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f)
    (hz : IsZeroAtImInfty f) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsZeroAt (heckeOperator k n f) k := by
  refine (OnePoint.isZeroAt_iff_forall_SL2Z hc).2 fun γ _ ↦ ?_
  change IsZeroAtImInfty (heckeOperator k n f ∣[k] SpecialLinearGroup.mapGL ℝ γ)
  rw [heckeOperator_slash_of_mem k n hf ⟨γ, rfl⟩]
  exact isZeroAtImInfty_heckeOperator k n hz

/-! ### Checks in small index -/

private lemma divisorsAntidiagonal_two : Nat.divisorsAntidiagonal 2 = {(1, 2), (2, 1)} := by
  decide

/-- `T_2` is the sum over the three representatives `!![1, 0; 0, 2]`, `!![1, 1; 0, 2]` and
`!![2, 0; 0, 1]`. -/
theorem heckeOperator_two (f : ℍ → ℂ) :
    heckeOperator k 2 f =
      f ∣[k] heckeMatrix 1 0 2 + f ∣[k] heckeMatrix 1 1 2 + f ∣[k] heckeMatrix 2 0 1 := by
  rw [heckeOperator, divisorsAntidiagonal_two]
  simp [sum_range_succ]

end ModularForm

/-! ### The operator on cusp forms -/

namespace CuspForm

variable (k : ℤ) (n : ℕ)

/-- **The Hecke operator `T_n` on `S_k(SL(2, ℤ))`**, as a map of cusp forms. Modularity is
`ModularForm.heckeOperator_slash_of_mem`, holomorphy is
`ModularForm.mdifferentiable_heckeOperator`, and vanishing at the cusps is
`ModularForm.isZeroAt_heckeOperator`. -/
noncomputable def heckeOperator (f : CuspForm 𝒮ℒ k) : CuspForm 𝒮ℒ k where
  toFun := ModularForm.heckeOperator k n f
  slash_action_eq' _ hγ :=
    ModularForm.heckeOperator_slash_of_mem k n (SlashInvariantForm.slash_action_eqn f) hγ
  holo' := ModularForm.mdifferentiable_heckeOperator k n (CuspFormClass.holo f)
  zero_at_cusps' hc := ModularForm.isZeroAt_heckeOperator k n
    (SlashInvariantForm.slash_action_eqn f) (CuspFormClass.zero_at_infty f) hc

/-- The underlying function of the bundled `T_n` is the unbundled one. -/
@[simp]
lemma coe_heckeOperator (f : CuspForm 𝒮ℒ k) :
    ⇑(heckeOperator k n f) = ModularForm.heckeOperator k n f := rfl

/-- **The Hecke operator `T_n` as a `ℂ`-linear endomorphism of `S_k(SL(2, ℤ))`.** -/
noncomputable def heckeOperatorₗ : Module.End ℂ (CuspForm 𝒮ℒ k) where
  toFun := heckeOperator k n
  map_add' f g := by ext τ; simp
  map_smul' c f := by ext τ; simp

/-- Evaluating the linear map `T_n` gives the bundled Hecke operator. -/
@[simp]
lemma heckeOperatorₗ_apply (f : CuspForm 𝒮ℒ k) : heckeOperatorₗ k n f = heckeOperator k n f :=
  rfl

end CuspForm

end
