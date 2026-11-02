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

public import FormalConjecturesUtil

/-!
# The generalized Lax conjecture

A homogeneous polynomial $p \in \mathbb{R}[x_1, \dots, x_n]$ of degree $d \ge 1$ is *hyperbolic*
with respect to $e \in \mathbb{R}^n$ if $p(e) \ne 0$ and, for every $x \in \mathbb{R}^n$, every
root of $t \mapsto p(te - x)$ is real. Its closed hyperbolicity cone $\Lambda_+(p, e)$ is the set
of $x$ for which all these roots are nonnegative. A cone is *spectrahedral* if it equals
$\{x : x_1 A_1 + \dots + x_n A_n \succeq 0\}$ for some real symmetric $N \times N$ matrices
$A_1, \dots, A_n$ with $N \ge 1$.

The (geometric) generalized Lax conjecture asserts that every hyperbolicity cone is
spectrahedral. For three variables this follows from the Helton–Vinnikov theorem [HV07], which
proves Lax's conjecture [LPR05]. Brändén [Br11] showed that the stronger determinantal form fails:
some hyperbolic polynomials have no power with a definite determinantal representation. OpenAI
[OAI26] disproved the geometric conjecture with an explicit hyperbolic polynomial of degree 20 in
23 variables.

*References:*
- [HV07] J. W. Helton and V. Vinnikov, *Linear matrix inequality representation of sets*,
  Comm. Pure Appl. Math. 60 (2007), 654–674.
- [LPR05] A. S. Lewis, P. A. Parrilo and M. V. Ramana, *The Lax conjecture is true*,
  Proc. Amer. Math. Soc. 133 (2005), 2495–2499.
- [Br11] P. Brändén, *Obstructions to determinantal representability*, Adv. Math. 226 (2011),
  1202–1212.
- [OAI26] OpenAI, *A nonspectrahedral hyperbolicity cone*. OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Nonspectrahedral-Hyperbolicity-Cone-September-24-2026/nonspectrahedral-hyperbolicity-cone.pdf
-/

@[expose] public section

namespace GeneralizedLaxConjecture

variable {σ : Type*}

/-- The polynomial $t \mapsto p(te - x)$. -/
noncomputable def linePolynomial (p : MvPolynomial σ ℝ) (e x : σ → ℝ) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (e i) * Polynomial.X - Polynomial.C (x i)) p

/-- `p` is hyperbolic with respect to `e`: it is homogeneous of positive degree, `p(e) ≠ 0`, and
for every `x` all roots of `t ↦ p(te - x)` are real. -/
def IsHyperbolic (p : MvPolynomial σ ℝ) (e : σ → ℝ) : Prop :=
  (∃ d, 0 < d ∧ p.IsHomogeneous d) ∧ MvPolynomial.eval e p ≠ 0 ∧
    ∀ (x : σ → ℝ) (z : ℂ), (linePolynomial p e x).aeval z = 0 → z.im = 0

/-- The closed hyperbolicity cone: the points `x` for which every root of `t ↦ p(te - x)` is real
and nonnegative. -/
def hyperbolicityCone (p : MvPolynomial σ ℝ) (e : σ → ℝ) : Set (σ → ℝ) :=
  {x | ∀ z : ℂ, (linePolynomial p e x).aeval z = 0 → z.im = 0 ∧ 0 ≤ z.re}

/-- A set `K ⊆ ℝⁿ` is spectrahedral if `K = {x | x₁ A₁ + ⋯ + xₙ Aₙ ⪰ 0}` for some real symmetric
`N × N` matrices `Aᵢ` with `N ≥ 1`. -/
def IsSpectrahedral {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∃ A : Fin n → Matrix (Fin N) (Fin N) ℝ, (∀ i, (A i).IsSymm) ∧
    K = {x | (∑ i, x i • A i).PosSemidef}

set_option linter.style.formal_proof_palomar false in
/--
**The generalized Lax conjecture, disproved.** Not every hyperbolicity cone is spectrahedral.

OpenAI [OAI26] gave an explicit counterexample in 23 variables; see
`generalized_lax_conjecture.variants.explicit` and the linked Lean proof.
-/
@[category research solved, AMS 14 90, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HyperbolicCones/Main.lean#L25"]
theorem generalized_lax_conjecture :
    ¬ ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (e : Fin n → ℝ),
      IsHyperbolic p e → IsSpectrahedral (hyperbolicityCone p e) := by
  sorry

/--
For three variables every hyperbolicity cone is spectrahedral: by the Helton–Vinnikov theorem
[HV07, LPR05], `p / p(e)` has a definite determinantal representation.
-/
@[category research solved, AMS 14 90]
theorem generalized_lax_conjecture.variants.three_variables (p : MvPolynomial (Fin 3) ℝ)
    (e : Fin 3 → ℝ) (hp : IsHyperbolic p e) : IsSpectrahedral (hyperbolicityCone p e) := by
  sorry

namespace Explicit

/-! The counterexample of [OAI26], copied from the OpenAI comparator challenge
`HyperbolicCones`. The ambient space is $\mathbb{S}^4 \times \mathbb{S}^4 \times \mathbb{R}^3$,
of dimension $10 + 10 + 3 = 23$, and the polynomial is
$p(X, Z, y) = \det((\det X) Z - \Phi_y(\operatorname{adj} X))$ with base point $(I_4, I_4, 0)$. -/

universe u

/-- Square matrices of size `n`. -/
abbrev Mat (n : ℕ) (R : Type u) := Matrix (Fin n) (Fin n) R

/-- Real symmetric matrices of size `n`. -/
abbrev Sym (n : ℕ) := selfAdjoint (Mat n ℝ)

instance instFiniteDimensionalSym (n : ℕ) : FiniteDimensional ℝ (Sym n) :=
  FiniteDimensional.finiteDimensional_submodule (selfAdjoint.submodule ℝ (Mat n ℝ))

/-- The ambient space `𝕊⁴ × 𝕊⁴ × ℝ³`. -/
abbrev Ambient := (Sym 4 × Sym 4) × (Fin 3 → ℝ)

/-- Indices `(i, j)` with `i ≤ j` of the upper triangle of a `4 × 4` matrix. -/
abbrev SymIndex := {ij : Fin 4 × Fin 4 // ij.1 ≤ ij.2}

/-- Coordinates on the ambient space. -/
abbrev Coord := (SymIndex ⊕ SymIndex) ⊕ Fin 3

/-- The matrix `Q(y)` of the Choi–Lam biquadratic form. -/
def qMatrix {R : Type u} [CommRing R] (y : Fin 3 → R) : Mat 3 R :=
  fun i j => if i = j then y i ^ 2 + y (i + 1) ^ 2 else -(y i * y j)

/-- The linear map `Φ_y : 𝕊⁴ → 𝕊⁴`. -/
def phi {R : Type u} [CommRing R] (y : Fin 3 → R) (X : Mat 4 R) : Mat 4 R :=
  fun i j => Fin.cases
    (Fin.cases
      (Matrix.trace (qMatrix y * X.submatrix Fin.succ Fin.succ))
      (fun j => -(∑ k, X 0 k.succ * qMatrix y k j)) j)
    (fun i => Fin.cases
      (-(∑ k, qMatrix y i k * X k.succ 0))
      (fun j => X 0 0 * qMatrix y i j) j) i

/-- `det((det X) Z - Φ_y(adj X))`. -/
def matrixValue {R : Type u} [CommRing R]
    (X Z : Mat 4 R) (y : Fin 3 → R) : R :=
  Matrix.det ((Matrix.det X) • Z - phi y (Matrix.adjugate X))

/-- The symmetric matrix with upper triangle `v`. -/
def symmetricCoordinates {R : Type u} (v : SymIndex → R) : Mat 4 R :=
  fun i j => if h : i ≤ j then v ⟨(i, j), h⟩
    else v ⟨(j, i), le_of_lt (lt_of_not_ge h)⟩

/-- The polynomial `p(X, Z, y)` in the 23 coordinates. -/
noncomputable def polynomial : MvPolynomial Coord ℝ :=
  matrixValue
    (symmetricCoordinates fun ij => MvPolynomial.X (Sum.inl (Sum.inl ij)))
    (symmetricCoordinates fun ij => MvPolynomial.X (Sum.inl (Sum.inr ij)))
    (fun i => MvPolynomial.X (Sum.inr i))

/-- The coordinates of a point of the ambient space. -/
def coordinates (x : Ambient) : Coord → ℝ :=
  Sum.elim (Sum.elim
    (fun ij => (x.1.1 : Mat 4 ℝ) ij.val.1 ij.val.2)
    (fun ij => (x.1.2 : Mat 4 ℝ) ij.val.1 ij.val.2)) x.2

/-- The base point `(I₄, I₄, 0)`. -/
def basePoint : Ambient := ((1, 1), 0)

/-- The polynomial `t ↦ p(t e - x)` for the base point `e`. -/
noncomputable def linePolynomial (x : Ambient) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (coordinates basePoint i) * Polynomial.X -
      Polynomial.C (coordinates x i)) polynomial

/-- The closed hyperbolicity cone of `p` at the base point. -/
def cone : Set Ambient :=
  {x | ∀ t : ℂ, (linePolynomial x).aeval t = 0 → t.im = 0 ∧ 0 ≤ t.re}

/-- Upper-triangular coordinates define a real self-adjoint matrix. -/
@[category API, AMS 14 90]
theorem symmetricCoordinates_isSelfAdjoint (v : SymIndex → ℝ) :
    IsSelfAdjoint (symmetricCoordinates v) := by
  change (symmetricCoordinates v).IsHermitian
  rw [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm.ext_iff]
  intro i j
  simp only [symmetricCoordinates]
  split_ifs with hji hij hij
  · have hij_eq : i = j := le_antisymm hij hji
    subst j
    rfl
  · rfl
  · rfl
  · omega

/-- Every assignment of the 23 coordinates comes from a point of the ambient space. -/
@[category API, AMS 14 90]
theorem coordinates_surjective : Function.Surjective coordinates := by
  intro v
  refine ⟨((⟨symmetricCoordinates (fun ij => v (Sum.inl (Sum.inl ij))),
    symmetricCoordinates_isSelfAdjoint _⟩,
    ⟨symmetricCoordinates (fun ij => v (Sum.inl (Sum.inr ij))),
    symmetricCoordinates_isSelfAdjoint _⟩), fun i => v (Sum.inr i)), ?_⟩
  funext i
  rcases i with (i | i) | i
  · simp [coordinates, symmetricCoordinates, i.property]
  · simp [coordinates, symmetricCoordinates, i.property]
  · rfl

/-- The coordinate map is real linear. -/
def coordinatesLinear : Ambient →ₗ[ℝ] (Coord → ℝ) where
  toFun := coordinates
  map_add' x y := by
    funext i
    rcases i with (i | i) | i <;> rfl
  map_smul' c x := by
    funext i
    rcases i with (i | i) | i <;> rfl

/-- Renaming the coordinates to `Fin 23` does not change the line polynomials. -/
@[category API, AMS 14 90]
theorem linePolynomial_rename (f : Coord ≃ Fin (Fintype.card Coord)) (x : Ambient) :
    GeneralizedLaxConjecture.linePolynomial (MvPolynomial.rename f polynomial)
      (coordinates basePoint ∘ f.symm) (coordinates x ∘ f.symm) = linePolynomial x := by
  simp [GeneralizedLaxConjecture.linePolynomial, linePolynomial,
    MvPolynomial.eval₂_rename, Function.comp_def]

end Explicit

open Explicit in
set_option linter.style.formal_proof_palomar false in
/--
The statement of the linked Lean proof [OAI26]: `p` is homogeneous of degree 20 on a space of
dimension 23, `p(e) = 1`, `p` is hyperbolic with respect to `e`, and its closed hyperbolicity
cone is not `{x | L x ⪰ 0}` for any linear map `L` into `N × N` real symmetric matrices, `N ≥ 1`.
-/
@[category research solved, AMS 14 90, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HyperbolicCones/Main.lean#L25"]
theorem generalized_lax_conjecture.variants.explicit :
    Module.finrank ℝ Ambient = 23 ∧
    polynomial.IsHomogeneous 20 ∧
    polynomial.totalDegree = 20 ∧
    MvPolynomial.eval (coordinates basePoint) polynomial = 1 ∧
    (∀ (x : Ambient) (z : ℂ), (Explicit.linePolynomial x).aeval z = 0 → z.im = 0) ∧
    ∀ (N : ℕ) (_hN : 0 < N) (L : Ambient →ₗ[ℝ] Sym N),
      cone ≠ {x | (L x : Mat N ℝ).PosSemidef} := by
  sorry

/-- The explicit counterexample disproves the generalized Lax conjecture. -/
@[category test, AMS 14 90]
theorem generalized_lax_conjecture_of_explicit
    (h : type_of% generalized_lax_conjecture.variants.explicit) :
    type_of% generalized_lax_conjecture := by
  classical
  let f := Fintype.equivFin Explicit.Coord
  let p := MvPolynomial.rename f Explicit.polynomial
  let e := Explicit.coordinates Explicit.basePoint ∘ f.symm
  have hp : IsHyperbolic p e := by
    refine ⟨⟨20, by norm_num, h.2.1.rename_isHomogeneous⟩, ?_, ?_⟩
    · have he : MvPolynomial.eval e p = 1 := by
        simpa [p, e, MvPolynomial.eval_rename, Function.comp_def] using h.2.2.2.1
      rw [he]
      exact one_ne_zero
    · intro v z hz
      obtain ⟨x, hx⟩ := Explicit.coordinates_surjective (v ∘ f)
      have hv : Explicit.coordinates x ∘ f.symm = v := by
        simp [hx, Function.comp_def]
      rw [← hv, Explicit.linePolynomial_rename] at hz
      exact h.2.2.2.2.1 x z hz
  intro hlax
  obtain ⟨N, hN, A, hA, hK⟩ := hlax _ p e hp
  let L : Explicit.Ambient →ₗ[ℝ] Explicit.Sym N :=
    ∑ i, ((LinearMap.proj (f.symm i)).comp Explicit.coordinatesLinear).smulRight
      ⟨A i, (Matrix.isHermitian_iff_isSymm.mpr (hA i)).isSelfAdjoint⟩
  apply h.2.2.2.2.2 N hN L
  ext x
  have hx : x ∈ Explicit.cone ↔
      (Explicit.coordinates x ∘ f.symm) ∈ hyperbolicityCone p e := by
    simp only [Explicit.cone, hyperbolicityCone, Set.mem_ofPred_eq, p, e,
      Explicit.linePolynomial_rename]
  rw [hx, hK]
  simp [L, Explicit.coordinatesLinear, Function.comp_def]

end GeneralizedLaxConjecture
