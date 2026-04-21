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

import FormalConjectures.Util.ProblemImports

noncomputable section

open scoped BigOperators

/-!
# Open Quantum Problem 23: SIC-POVMs

## Mathematical problem
The OQP page presents three increasingly strong formulations of this problem.
In this file we formalize the first one, closest to the physics terminology:
existence of a symmetric informationally complete POVM in every finite dimension.

A SIC-POVM in dimension $d$ can be represented by a family of $d^2$ normalized
vectors in $\mathbb{C}^d$ whose pairwise squared overlaps are all equal to
$(d + 1)^{-1}$. We encode such a family as a map `Fin (d ^ 2) → StateVector d`.

## Background
SIC-POVMs are a basic structure in finite-dimensional quantum information.
They are closely related to equiangular lines, tight frames, quantum state
reconstruction, and finite-dimensional measurement theory.
The open problem asks whether such families exist in every dimension.

## What this file formalizes
This file formalizes the existence problem for symmetric informationally complete
POVMs through the predicate `HasSICPOVM d`.
More precisely, it contains the following layers.
### Core API
The main definitions formalized in this file are:
- `StateVector d`: a state vector in `ℂ^d`;
- `mkStateVector`: constructor from coordinates in the computational basis;
- `IsNormalized ψ`: normalization predicate for a state vector;
- `overlapSq φ ψ`: squared magnitude of the inner-product overlap;
- `HasConstantOverlapSq c Φ`: constant pairwise squared-overlap condition;
- `sicOverlapSq d`: the SIC overlap value `(d + 1)⁻¹`;
- `IsSICFamily d Φ`: the predicate that a family of `d^2` vectors in `ℂ^d`
  is a SIC family;
- `HasSICPOVM d`: existence of a SIC family in dimension `d`.
In addition, the file includes explicit witness families and convenient
constructors used in the low-dimensional benchmark cases:
- `vec2`, `vec3`;
- `qubitSICFamily`;
- `hesseFamily`;
- `bb84Family`.
### Complete open conjecture
The main open theorem is:
- `sicPOVMs`, expressing the conjecture that for every `d ≥ 1`, there exists a
  SIC-POVM in dimension `d`.
### Special cases
The file also isolates several special cases:
- solved low-dimensional benchmark cases:
  `hasSICPOVM_zero`, `hasSICPOVM_one`, `hasSICPOVM_two`, `hasSICPOVM_three`;
- a negative benchmark result:
  `bb84Family_not_isSICFamily`, showing that the BB84 family in dimension `2`
  does not form a SIC family;
- selected open benchmark dimensions:
  `hasSICPOVM_56`, `hasSICPOVM_58`, `hasSICPOVM_59`, `hasSICPOVM_60`,
  `hasSICPOVM_64`, `hasSICPOVM_68`, `hasSICPOVM_69`, `hasSICPOVM_70`,
  `hasSICPOVM_71`, `hasSICPOVM_72`, `hasSICPOVM_75`.
### Test lemmas
The file includes the following test lemmas and benchmark-support statements:
- `hasConstantOverlapSq_singleton`;
- `sicOverlapSq_one`, `sicOverlapSq_two`, `sicOverlapSq_three`,
  `sicOverlapSq_pos`;
- `isSICFamily_singleton_iff`, `isSICFamily_one_of_normalized`;
- `qubitSICFamily_normalized`, `qubitSICFamily_pairwise`;
- `hesseFamily_normalized`, `hesseFamily_pairwise`;
- `bb84Family_normalized`.

## References
*Primary source list entry:*
- IQOQI Vienna Open Quantum Problems, problem 23:
  https://oqp.iqoqi.oeaw.ac.at/sic-povms-and-zauners-conjecture
- Formal Conjectures issue #1823:
  https://github.com/google-deepmind/formal-conjectures/issues/1823

### Foundational references
- J. M. Renes, R. Blume-Kohout, A. J. Scott, and M. C. Caves,
  *Symmetric informationally complete quantum measurements*,
  J. Math. Phys. 45, 2171-2180 (2004), arXiv:quant-ph/0310075.
- G. Zauner,
  *Quantum Designs: Foundations of a Noncommutative Design Theory*,
  PhD thesis, University of Vienna (1999).
-/

namespace OpenQuantumProblem23

/- ## Basic structures -/

/-- A state vector in the $d$-dimensional complex Hilbert space $\mathbb{C}^d$. -/
abbrev StateVector (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- Build a state vector from its coordinates in the computational basis. -/
abbrev mkStateVector {d : ℕ} (ψ : Fin d → ℂ) : StateVector d := WithLp.toLp 2 ψ

/-- Coercion from a state vector to its coordinate function. -/
instance {d : ℕ} : CoeFun (StateVector d) (fun _ => Fin d → ℂ) where
  coe ψ := ψ.ofLp

/-- A state built from coordinates has those coordinates as its entries. -/
@[simp, category API, AMS 15 47 81]
lemma mkStateVector_apply {d : ℕ} (ψ : Fin d → ℂ) (i : Fin d) :
    mkStateVector ψ i = ψ i := rfl

/-- A state vector is normalized if it has $L^2$ norm $1$. -/
def IsNormalized {d : ℕ} (ψ : StateVector d) : Prop := ‖ψ‖ = 1

/-- A state is normalized iff its squared norm is $1$. -/
@[category API, AMS 15 47 81]
lemma isNormalized_iff_norm_sq_eq_one {d : ℕ} (ψ : StateVector d) :
    IsNormalized ψ ↔ ‖ψ‖ ^ (2 : ℕ) = 1 := by
  rw [IsNormalized]
  constructor
  · intro h
    calc
      ‖ψ‖ ^ (2 : ℕ) = (1 : ℝ) ^ (2 : ℕ) := by simp [h]
      _ = 1 := by norm_num
  · intro h
    have h' : ‖ψ‖ * ‖ψ‖ = 1 := by
      simpa [pow_two] using h
    have hnonneg : 0 ≤ ‖ψ‖ := norm_nonneg ψ
    nlinarith

/-- The squared $L^2$ norm of a state is the sum of the squared norms of its coordinates. -/
@[category API, AMS 15 47 81]
lemma norm_sq_eq_sum_coord_norm_sq {d : ℕ} (ψ : StateVector d) :
    ‖ψ‖ ^ (2 : ℕ) = ∑ i : Fin d, ‖ψ i‖ ^ (2 : ℕ) := by
  simpa using EuclideanSpace.norm_sq_eq ψ

/-- A normalization criterion in terms of the coordinate-wise complex norm-squared sum. -/
@[category API, AMS 15 47 81]
lemma isNormalized_of_coord_normSq_sum_one {d : ℕ} (ψ : StateVector d)
    (hψ : ∑ i : Fin d, Complex.normSq (ψ i) = 1) : IsNormalized ψ := by
  rw [isNormalized_iff_norm_sq_eq_one]
  calc
    ‖ψ‖ ^ (2 : ℕ) = ∑ i : Fin d, ‖ψ i‖ ^ (2 : ℕ) := norm_sq_eq_sum_coord_norm_sq ψ
    _ = ∑ i : Fin d, Complex.normSq (ψ i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa using (RCLike.normSq_eq_def' (ψ i)).symm
    _ = 1 := hψ

/-- The squared magnitude of the overlap between two state vectors. -/
def overlapSq {d : ℕ} (φ ψ : StateVector d) : ℝ :=
  Complex.normSq (∑ i : Fin d, star (φ i) * ψ i)

/-- A family has constant pairwise squared overlap $c$ if every two distinct members have squared overlap $c$. -/
def HasConstantOverlapSq {d N : ℕ} (c : ℝ) (Φ : Fin N → StateVector d) : Prop :=
  Pairwise fun i j => overlapSq (Φ i) (Φ j) = c

/-- The squared overlap value of a SIC family in dimension $d$. -/
def sicOverlapSq (d : ℕ) : ℝ := (d + 1 : ℝ)⁻¹

/-- A SIC family in dimension $d$ consists of $d^2$ normalized vectors in $\mathbb{C}^d$ with pairwise squared overlap $(d + 1)^{-1}$. -/
def IsSICFamily (d : ℕ) (Φ : Fin (d ^ 2) → StateVector d) : Prop :=
  (∀ i, IsNormalized (Φ i)) ∧ HasConstantOverlapSq (sicOverlapSq d) Φ

/-- There exists a SIC-POVM in dimension $d$. -/
def HasSICPOVM (d : ℕ) : Prop := ∃ Φ : Fin (d ^ 2) → StateVector d, IsSICFamily d Φ

/- ## Basic API and benchmark cases -/

/-- Any singleton family has constant pairwise squared overlap, vacuously. -/
@[category test, AMS 15 47 81]
lemma hasConstantOverlapSq_singleton {d : ℕ} (c : ℝ) (ψ : StateVector d) :
    HasConstantOverlapSq c (fun _ : Fin 1 => ψ) := by
  intro i j hij
  exact (hij (Subsingleton.elim i j)).elim

/-- The SIC overlap value in dimension $1$ is $1/2$. -/
@[category test, AMS 15 47 81]
lemma sicOverlapSq_one : sicOverlapSq 1 = (1 / 2 : ℝ) := by
  norm_num [sicOverlapSq]

/-- The SIC overlap value is positive in every dimension. -/
@[category test, AMS 15 47 81]
lemma sicOverlapSq_pos (d : ℕ) : 0 < sicOverlapSq d := by
  dsimp [sicOverlapSq]
  have h : 0 < (d + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos d
  exact inv_pos.mpr h

/-- In dimension $1$, a singleton family is SIC exactly when its vector is normalized. -/
@[category test, AMS 15 47 81]
lemma isSICFamily_singleton_iff {ψ : StateVector 1} :
    IsSICFamily 1 (fun _ : Fin 1 => ψ) ↔ IsNormalized ψ := by
  constructor
  · intro h
    simpa using h.1 0
  · intro h
    constructor
    · intro i
      simpa using h
    · simpa using hasConstantOverlapSq_singleton (d := 1) (c := sicOverlapSq 1) ψ

/-- The empty family witnesses the degenerate dimension-$0$ case. -/
@[category test, AMS 15 47 81]
theorem hasSICPOVM_zero : HasSICPOVM 0 := by
  refine ⟨fun i : Fin (0 ^ 2) => Fin.elim0 i, ?_⟩
  constructor
  · intro i
    exact Fin.elim0 i
  · intro i j hij
    exact Fin.elim0 i

/-- Any normalized state in dimension $1$ yields a SIC family. -/
@[category test, AMS 15 47 81]
lemma isSICFamily_one_of_normalized {ψ : StateVector 1} (hψ : IsNormalized ψ) :
    IsSICFamily 1 (fun _ : Fin 1 => ψ) := by
  exact isSICFamily_singleton_iff.2 hψ

/-- Dimension $1$ admits a SIC-POVM. -/
@[category test, AMS 15 47 81]
theorem hasSICPOVM_one : HasSICPOVM 1 := by
  let v : StateVector 1 := mkStateVector (fun _ : Fin 1 => (1 : ℂ))
  have hv_nonzero : v ≠ 0 := by
    intro hv
    have h1 : v 0 = (1 : ℂ) := by
      simp [v]
    have h0 : (0 : StateVector 1) 0 = (0 : ℂ) := by
      simp
    have : (1 : ℂ) = 0 := by
      rw [← h1, hv, h0]
    exact one_ne_zero this
  let ψ : StateVector 1 := (‖v‖)⁻¹ • v
  have hψ_norm : IsNormalized ψ := by
    show ‖(‖v‖)⁻¹ • v‖ = 1
    rw [norm_smul]
    have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_nonzero
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv_norm_pos)]
    rw [inv_mul_cancel₀ hv_norm_pos.ne']
  refine ⟨fun _ : Fin 1 => ψ, ?_⟩
  exact isSICFamily_one_of_normalized hψ_norm

/- ## Explicit low-dimensional witnesses -/

/-- The standard algebraic primitive cube root of unity. -/
def ω : ℂ := ((-(1 : ℝ) / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I

/-- The first real amplitude used in the tetrahedral qubit SIC. -/
def tetraA : ℝ := Real.sqrt (1 / 3)

/-- The second real amplitude used in the tetrahedral qubit SIC. -/
def tetraB : ℝ := Real.sqrt (2 / 3)

/-- The common scale used in the Hesse qutrit SIC. -/
def hesseS : ℝ := Real.sqrt (1 / 2)

/-- A convenient constructor for qubit state vectors. -/
def vec2 (z₀ z₁ : ℂ) : StateVector 2 := mkStateVector ![z₀, z₁]

/-- A convenient constructor for qutrit state vectors. -/
def vec3 (z₀ z₁ z₂ : ℂ) : StateVector 3 := mkStateVector ![z₀, z₁, z₂]

/-- The first coordinate of a qubit state built with `vec2`. -/
@[simp, category API, AMS 15 47 81]
lemma vec2_apply_zero (z₀ z₁ : ℂ) : vec2 z₀ z₁ 0 = z₀ := by rfl

/-- The second coordinate of a qubit state built with `vec2`. -/
@[simp, category API, AMS 15 47 81]
lemma vec2_apply_one (z₀ z₁ : ℂ) : vec2 z₀ z₁ 1 = z₁ := by rfl

/-- The first coordinate of a qutrit state built with `vec3`. -/
@[simp, category API, AMS 15 47 81]
lemma vec3_apply_zero (z₀ z₁ z₂ : ℂ) : vec3 z₀ z₁ z₂ 0 = z₀ := by rfl

/-- The second coordinate of a qutrit state built with `vec3`. -/
@[simp, category API, AMS 15 47 81]
lemma vec3_apply_one (z₀ z₁ z₂ : ℂ) : vec3 z₀ z₁ z₂ 1 = z₁ := by rfl

/-- The third coordinate of a qutrit state built with `vec3`. -/
@[simp, category API, AMS 15 47 81]
lemma vec3_apply_two (z₀ z₁ z₂ : ℂ) : vec3 z₀ z₁ z₂ 2 = z₂ := by rfl

/-- The square of $\mathrm{tetraA}$ is $1/3$. -/
@[category API, AMS 15 47 81]
lemma tetraA_sq : tetraA ^ (2 : ℕ) = (1 / 3 : ℝ) := by
  unfold tetraA
  have h : 0 ≤ (1 / 3 : ℝ) := by positivity
  nlinarith [Real.sq_sqrt h]

/-- The square of $\mathrm{tetraB}$ is $2/3$. -/
@[category API, AMS 15 47 81]
lemma tetraB_sq : tetraB ^ (2 : ℕ) = (2 / 3 : ℝ) := by
  unfold tetraB
  have h : 0 ≤ (2 / 3 : ℝ) := by positivity
  nlinarith [Real.sq_sqrt h]

/-- The square of $\mathrm{hesseS}$ is $1/2$. -/
@[category API, AMS 15 47 81]
lemma hesseS_sq : hesseS ^ (2 : ℕ) = (1 / 2 : ℝ) := by
  unfold hesseS
  have h : 0 ≤ (1 / 2 : ℝ) := by positivity
  nlinarith [Real.sq_sqrt h]

/-- The product $\mathrm{tetraA}\,\mathrm{tetraA}$ is $1/3$. -/
@[simp, category API, AMS 15 47 81]
lemma tetraA_mul_self : tetraA * tetraA = (1 / 3 : ℝ) := by
  simpa [pow_two] using tetraA_sq

/-- The product $\mathrm{tetraB}\,\mathrm{tetraB}$ is $2/3$. -/
@[simp, category API, AMS 15 47 81]
lemma tetraB_mul_self : tetraB * tetraB = (2 / 3 : ℝ) := by
  simpa [pow_two] using tetraB_sq

/-- The product $\mathrm{hesseS}\,\mathrm{hesseS}$ is $1/2$. -/
@[simp, category API, AMS 15 47 81]
lemma hesseS_mul_self : hesseS * hesseS = (1 / 2 : ℝ) := by
  simpa [pow_two] using hesseS_sq

/-- The square of $\sqrt{3}$ is $3$. -/
@[category test, AMS 15 47 81]
lemma sq_sqrt_three : (Real.sqrt 3) ^ (2 : ℕ) = (3 : ℝ) := by
  have h : 0 ≤ (3 : ℝ) := by positivity
  nlinarith [Real.sq_sqrt h]

/-- The complex square of $\mathrm{tetraA}$ equals $1/3$. -/
@[simp, category API, AMS 15 47 81]
lemma tetraA_sq_complex : ((tetraA : ℂ) * tetraA) = (1 / 3 : ℂ) := by
  have h : (((tetraA * tetraA : ℝ)) : ℂ) = (1 / 3 : ℂ) := by
    norm_num [tetraA_mul_self]
  simpa only [Complex.ofReal_mul] using h

/-- The complex square of $\mathrm{tetraB}$ equals $2/3$. -/
@[simp, category API, AMS 15 47 81]
lemma tetraB_sq_complex : ((tetraB : ℂ) * tetraB) = (2 / 3 : ℂ) := by
  have h : (((tetraB * tetraB : ℝ)) : ℂ) = (2 / 3 : ℂ) := by
    norm_num [tetraB_mul_self]
  simpa only [Complex.ofReal_mul] using h

/-- The complex square of $\mathrm{hesseS}$ equals $1/2$. -/
@[simp, category API, AMS 15 47 81]
lemma hesseS_sq_complex : ((hesseS : ℂ) * hesseS) = (1 / 2 : ℂ) := by
  have h : (((hesseS * hesseS : ℝ)) : ℂ) = (1 / 2 : ℂ) := by
    norm_num [hesseS_mul_self]
  simpa only [Complex.ofReal_mul] using h

/-- The complex norm-squared of $\mathrm{tetraA}$ equals $1/3$. -/
@[simp, category API, AMS 15 47 81]
lemma tetraA_normSq : Complex.normSq (tetraA : ℂ) = (1 / 3 : ℝ) := by
  rw [Complex.normSq_ofReal]
  nlinarith [tetraA_sq]

/-- The complex norm-squared of $\mathrm{tetraB}$ equals $2/3$. -/
@[simp, category API, AMS 15 47 81]
lemma tetraB_normSq : Complex.normSq (tetraB : ℂ) = (2 / 3 : ℝ) := by
  rw [Complex.normSq_ofReal]
  nlinarith [tetraB_sq]

/-- The complex norm-squared of $\mathrm{hesseS}$ equals $1/2$. -/
@[simp, category API, AMS 15 47 81]
lemma hesseS_normSq : Complex.normSq (hesseS : ℂ) = (1 / 2 : ℝ) := by
  rw [Complex.normSq_ofReal]
  nlinarith [hesseS_sq]

/-- An explicit closed form for $\omega^2$. -/
@[simp, category API, AMS 15 47 81]
lemma omega_sq :
    ω ^ 2 = ((-(1 : ℝ) / 2 : ℝ) : ℂ) - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [ω, pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.sub_re]
    nlinarith [sq_sqrt_three]
  · simp [ω, pow_two, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_im]
    ring_nf

/-- Complex conjugation sends $\omega$ to $\omega^2$. -/
@[simp, category API, AMS 15 47 81]
lemma star_omega : star ω = ω ^ 2 := by
  rw [omega_sq]
  apply Complex.ext <;> simp [ω]

/-- Complex conjugation sends $\omega^2$ to $\omega$. -/
@[simp, category API, AMS 15 47 81]
lemma star_omega_sq : star (ω ^ 2) = ω := by
  rw [omega_sq]
  apply Complex.ext <;> simp [ω]

/-- The complex norm-squared of $\omega$ is $1$. -/
@[simp, category API, AMS 15 47 81]
lemma omega_normSq : Complex.normSq ω = 1 := by
  rw [ω, Complex.normSq_add_mul_I]
  nlinarith [sq_sqrt_three]

/-- The complex norm-squared of $\omega^2$ is $1$. -/
@[simp, category API, AMS 15 47 81]
lemma omega_sq_normSq : Complex.normSq (ω ^ 2) = 1 := by
  simp [pow_two, Complex.normSq_mul]

/-- The explicit closed form of $\omega^2$ has norm-squared $1$. -/
@[simp, category API, AMS 15 47 81]
lemma explicit_omega_sq_normSq :
    Complex.normSq (((-(1 : ℝ) / 2 : ℝ) : ℂ) - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [← omega_sq]
  simpa using omega_sq_normSq

/-- The explicit negative-half expression equals $\omega^2$. -/
@[category API, AMS 15 47 81]
lemma explicit_neg_half_sub_sqrt_three_half_mul_I_eq_omega_sq :
    (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I) = ω ^ 2 := by
  rw [omega_sq]
  apply Complex.ext
  · simp
    ring_nf
  · simp

/-- The equivalent $-\tfrac12 - i\tfrac{\sqrt3}{2}$ expression equals $\omega^2$. -/
@[category API, AMS 15 47 81]
lemma explicit_neg_half_sub_I_mul_sqrt_three_half_eq_omega_sq :
    (-(1 / 2 : ℂ) - Complex.I * ((Real.sqrt 3 : ℂ) / 2)) = ω ^ 2 := by
  simpa [mul_comm] using explicit_neg_half_sub_sqrt_three_half_mul_I_eq_omega_sq

/-- The explicit $-\tfrac12 + i\tfrac{\sqrt3}{2}$ expression equals $\omega$. -/
@[category API, AMS 15 47 81]
lemma explicit_neg_half_add_I_mul_sqrt_three_half_eq_omega :
    (-(1 / 2 : ℂ) + Complex.I * ((Real.sqrt 3 : ℂ) / 2)) = ω := by
  apply Complex.ext
  · simp [ω]
    ring_nf
  · simp [ω]

/-- The explicit negative-half expression for $\omega^2$ has norm-squared $1$. -/
@[simp, category API, AMS 15 47 81]
lemma explicit_neg_half_sub_sqrt_three_half_mul_I_normSq :
    Complex.normSq (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I) = 1 := by
  rw [explicit_neg_half_sub_sqrt_three_half_mul_I_eq_omega_sq]
  simpa using omega_sq_normSq

/-- The equivalent $-\tfrac12 - i\tfrac{\sqrt3}{2}$ expression has norm-squared $1$. -/
@[simp, category API, AMS 15 47 81]
lemma explicit_neg_half_sub_I_mul_sqrt_three_half_normSq :
    Complex.normSq (-(1 / 2 : ℂ) - Complex.I * ((Real.sqrt 3 : ℂ) / 2)) = 1 := by
  rw [explicit_neg_half_sub_I_mul_sqrt_three_half_eq_omega_sq]
  simpa using omega_sq_normSq

/-- A normalization identity used in the qubit SIC calculations. -/
@[simp, category test, AMS 15 47 81]
lemma one_third_add_two_thirds_mul_explicit_neg_half_sub_sqrt_three_half_mul_I_normSq :
    (1 / 3 : ℝ) + (2 / 3 : ℝ) *
      Complex.normSq (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I) = 1 := by
  rw [explicit_neg_half_sub_sqrt_three_half_mul_I_normSq]
  norm_num

/-- A normalization identity used in the qutrit SIC calculations. -/
@[simp, category test, AMS 15 47 81]
lemma one_half_add_one_half_mul_explicit_neg_half_sub_sqrt_three_half_mul_I_normSq :
    (1 / 2 : ℝ) + (1 / 2 : ℝ) *
      Complex.normSq (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I) = 1 := by
  rw [explicit_neg_half_sub_sqrt_three_half_mul_I_normSq]
  norm_num

/-- A rearranged normalization identity used in the qutrit SIC calculations. -/
@[simp, category test, AMS 15 47 81]
lemma one_half_mul_explicit_neg_half_sub_sqrt_three_half_mul_I_normSq_add_one_half :
    (1 / 2 : ℝ) * Complex.normSq (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I)
      + (1 / 2 : ℝ) = 1 := by
  rw [explicit_neg_half_sub_sqrt_three_half_mul_I_normSq]
  norm_num

/-- Multiplying $\omega$ by itself gives $\omega^2$. -/
@[simp, category test, AMS 15 47 81]
lemma omega_mul_omega : ω * ω = ω ^ 2 := by
  ring

/-- A complex number commutes with a real scalar embedded into $\mathbb{C}$. -/
@[simp, category test, AMS 15 47 81]
lemma mul_ofReal_comm (z : ℂ) (r : ℝ) : z * (r : ℂ) = (r : ℂ) * z := by
  ring

/-- Squaring the tetrahedral amplitude inside a product yields $(2/3)z$. -/
@[simp, category test, AMS 15 47 81]
lemma tetraB_sq_mul (z : ℂ) :
    (tetraB : ℂ) * ((tetraB : ℂ) * z) = (2 / 3 : ℂ) * z := by
  calc
    (tetraB : ℂ) * ((tetraB : ℂ) * z) = (((tetraB : ℂ) * tetraB) * z) := by ring
    _ = (2 / 3 : ℂ) * z := by simp

/-- Squaring the Hesse scale inside a product yields $(1/2)z$. -/
@[simp, category test, AMS 15 47 81]
lemma hesseS_sq_mul (z : ℂ) :
    (hesseS : ℂ) * ((hesseS : ℂ) * z) = (1 / 2 : ℂ) * z := by
  calc
    (hesseS : ℂ) * ((hesseS : ℂ) * z) = (((hesseS : ℂ) * hesseS) * z) := by ring
    _ = (1 / 2 : ℂ) * z := by simp

/-- The primitive cube root satisfies $\omega^3 = 1$. -/
@[simp, category API, AMS 15 47 81]
lemma omega_cubed : ω ^ 3 = 1 := by
  calc
    ω ^ 3 = ω * (ω ^ 2) := by ring
    _ = 1 := by
      rw [omega_sq]
      apply Complex.ext
      · simp [ω, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.sub_re]
        nlinarith [sq_sqrt_three]
      · simp [ω, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_im]
        ring_nf

/-- The primitive cube root satisfies $\omega^4 = \omega$. -/
@[simp, category API, AMS 15 47 81]
lemma omega_four : ω ^ 4 = ω := by
  calc
    ω ^ 4 = ω ^ 3 * ω := by ring
    _ = ω := by simp

/-- The product $\omega\omega^2$ equals $1$. -/
@[simp, category test, AMS 15 47 81]
lemma omega_mul_omega_sq : ω * (ω ^ 2) = 1 := by
  calc
    ω * (ω ^ 2) = ω ^ 3 := by ring
    _ = 1 := omega_cubed

/-- The product $\omega^2\omega$ equals $1$. -/
@[simp, category API, AMS 15 47 81]
lemma omega_sq_mul_omega : (ω ^ 2) * ω = 1 := by
  calc
    (ω ^ 2) * ω = ω ^ 3 := by ring
    _ = 1 := omega_cubed

/-- The product $\omega^2\omega^2$ equals $\omega$. -/
@[simp, category API, AMS 15 47 81]
lemma omega_sq_mul_omega_sq : (ω ^ 2) * (ω ^ 2) = ω := by
  calc
    (ω ^ 2) * (ω ^ 2) = ω ^ 4 := by ring
    _ = ω := omega_four

/-- The product $\overline{\omega}\omega$ equals $1$. -/
@[simp, category API, AMS 15 47 81]
lemma star_omega_mul_omega : star ω * ω = 1 := by
  rw [star_omega]
  simpa using omega_sq_mul_omega

/-- The product $\overline{\omega}\omega^2$ equals $\omega$. -/
@[simp, category API, AMS 15 47 81]
lemma star_omega_mul_omega_sq : star ω * (ω ^ 2) = ω := by
  rw [star_omega]
  simpa using omega_sq_mul_omega_sq

/-- The product $\overline{\omega^2}\omega$ equals $\omega^2$. -/
@[simp, category API, AMS 15 47 81]
lemma star_omega_sq_mul_omega : star (ω ^ 2) * ω = ω ^ 2 := by
  rw [star_omega_sq]
  simp

/-- The product $\overline{\omega^2}\omega^2$ equals $1$. -/
@[simp, category API, AMS 15 47 81]
lemma star_omega_sq_mul_omega_sq : star (ω ^ 2) * (ω ^ 2) = 1 := by
  rw [star_omega_sq]
  simpa using omega_mul_omega_sq

/-- The complex norm-squared of $1 + \omega$ is $1$. -/
@[simp, category API, AMS 15 47 81]
lemma normSq_one_add_omega : Complex.normSq (1 + ω) = 1 := by
  have hrewrite :
      1 + ω = ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
    simp [ω]
    ring
  rw [hrewrite, Complex.normSq_add_mul_I]
  nlinarith [sq_sqrt_three]

/-- The complex norm-squared of $1 + \omega^2$ is $1$. -/
@[simp, category API, AMS 15 47 81]
lemma normSq_one_add_omega_sq : Complex.normSq (1 + ω ^ 2) = 1 := by
  rw [omega_sq]
  have hrewrite :
      1 + (((-(1 : ℝ) / 2 : ℝ) : ℂ) - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I)
        = ((1 / 2 : ℝ) : ℂ) + ((-(Real.sqrt 3) / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp <;> ring
  rw [hrewrite, Complex.normSq_add_mul_I]
  nlinarith [sq_sqrt_three]

/-- The complex norm-squared of $1 + 2\omega$ is $3$. -/
@[simp, category API, AMS 15 47 81]
lemma normSq_one_add_two_mul_omega : Complex.normSq (1 + 2 * ω) = 3 := by
  have hrewrite :
      1 + 2 * ω = ((0 : ℝ) : ℂ) + ((Real.sqrt 3 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [ω] <;> ring
  rw [hrewrite, Complex.normSq_add_mul_I]
  nlinarith [sq_sqrt_three]

/-- The complex norm-squared of $1 + 2\omega^2$ is $3$. -/
@[simp, category API, AMS 15 47 81]
lemma normSq_one_add_two_mul_omega_sq : Complex.normSq (1 + 2 * (ω ^ 2)) = 3 := by
  rw [omega_sq]
  have hrewrite :
      1 + 2 * (((( -(1 : ℝ) / 2 : ℝ) : ℂ) - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I)
      ) = ((0 : ℝ) : ℂ) + ((-(Real.sqrt 3) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp <;> ring
  rw [hrewrite, Complex.normSq_add_mul_I]
  nlinarith [sq_sqrt_three]

/-- A standard qubit SIC overlap involving $\omega$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_qubit_offdiag_omega :
    Complex.normSq ((1 / 3 : ℂ) + (2 / 3 : ℂ) * ω) = (1 / 3 : ℝ) := by
  have hrewrite : ((1 / 3 : ℂ) + (2 / 3 : ℂ) * ω) = ((1 / 3 : ℂ) * (1 + 2 * ω)) := by
    ring
  rw [hrewrite, Complex.normSq_mul, normSq_one_add_two_mul_omega]
  norm_num [Complex.normSq_ofReal]

/-- A standard qubit SIC overlap involving $\omega^2$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_qubit_offdiag_omega_sq :
    Complex.normSq ((1 / 3 : ℂ) + (2 / 3 : ℂ) * (ω ^ 2)) = (1 / 3 : ℝ) := by
  have hrewrite :
      ((1 / 3 : ℂ) + (2 / 3 : ℂ) * (ω ^ 2)) = ((1 / 3 : ℂ) * (1 + 2 * (ω ^ 2))) := by
    ring
  rw [hrewrite, Complex.normSq_mul, normSq_one_add_two_mul_omega_sq]
  norm_num [Complex.normSq_ofReal]

/-- The same qubit SIC overlap written with the scalar on the left. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_qubit_offdiag_omega_left :
    Complex.normSq ((1 / 3 : ℂ) + ω * (2 / 3 : ℂ)) = (1 / 3 : ℝ) := by
  simpa [mul_comm] using normSq_qubit_offdiag_omega

/-- The same qubit SIC overlap with $\omega^2$ and the scalar on the left. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_qubit_offdiag_omega_sq_left :
    Complex.normSq ((1 / 3 : ℂ) + (ω ^ 2) * (2 / 3 : ℂ)) = (1 / 3 : ℝ) := by
  simpa [mul_comm] using normSq_qubit_offdiag_omega_sq

/-- A qubit SIC overlap written using complex conjugation of $\omega$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_qubit_offdiag_star_omega :
    Complex.normSq ((1 / 3 : ℂ) + (2 / 3 : ℂ) * star ω) = (1 / 3 : ℝ) := by
  rw [star_omega]
  simpa using normSq_qubit_offdiag_omega_sq

/-- A qubit SIC overlap written with the explicit closed form for $\omega$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_qubit_offdiag_explicit_omega :
    Complex.normSq ((1 / 3 : ℂ) + (2 / 3 : ℂ) *
      (-(1 / 2 : ℂ) + ((Real.sqrt 3 : ℂ) / 2) * Complex.I)) = (1 / 3 : ℝ) := by
  have h :
      (-(1 / 2 : ℂ) + ((Real.sqrt 3 : ℂ) / 2) * Complex.I)
        = (-(1 / 2 : ℂ) + Complex.I * ((Real.sqrt 3 : ℂ) / 2)) := by
    ring
  rw [h, explicit_neg_half_add_I_mul_sqrt_three_half_eq_omega]
  simpa using normSq_qubit_offdiag_omega

/-- A qubit SIC overlap using $\overline{\omega}$ and the explicit $\omega^2$ form. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_qubit_offdiag_star_omega_mul_explicit_omega_sq :
    Complex.normSq ((1 / 3 : ℂ) +
      (tetraB : ℂ) * star ω * ((tetraB : ℂ) *
        (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I))) = (1 / 3 : ℝ) := by
  rw [star_omega, explicit_neg_half_sub_sqrt_three_half_mul_I_eq_omega_sq]
  ring_nf
  simpa only [pow_two, tetraB_sq_complex, omega_four] using normSq_qubit_offdiag_omega

/-- A qubit SIC overlap using the explicit $\omega$ form and an extra factor of $\omega$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_qubit_offdiag_tetraB_explicit_omega_mul_omega :
    Complex.normSq ((1 / 3 : ℂ) +
      (tetraB : ℂ) * (-(1 / 2 : ℂ) + ((Real.sqrt 3 : ℂ) / 2) * Complex.I) *
        ((tetraB : ℂ) * ω)) = (1 / 3 : ℝ) := by
  have h :
      (-(1 / 2 : ℂ) + ((Real.sqrt 3 : ℂ) / 2) * Complex.I)
        = (-(1 / 2 : ℂ) + Complex.I * ((Real.sqrt 3 : ℂ) / 2)) := by
    ring
  rw [h, explicit_neg_half_add_I_mul_sqrt_three_half_eq_omega]
  ring_nf
  simpa only [pow_two, tetraB_sq_complex] using normSq_qubit_offdiag_omega_sq

/-- A qubit SIC overlap written using `starRingEnd` on $\omega`. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_qubit_offdiag_star_omega_exact :
    Complex.normSq ((1 / 3 : ℂ) + (2 / 3 : ℂ) * (starRingEnd ℂ) ω) = (1 / 3 : ℝ) := by
  change Complex.normSq ((1 / 3 : ℂ) + (2 / 3 : ℂ) * star ω) = (1 / 3 : ℝ)
  simpa using normSq_qubit_offdiag_star_omega

/-- A qubit SIC overlap using `starRingEnd` together with the explicit $\omega^2$ form. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_qubit_offdiag_star_omega_mul_explicit_omega_sq_exact :
    Complex.normSq ((1 / 3 : ℂ) +
      (tetraB : ℂ) * (starRingEnd ℂ) ω *
        ((tetraB : ℂ) * (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I))) = (1 / 3 : ℝ) := by
  change Complex.normSq ((1 / 3 : ℂ) +
      (tetraB : ℂ) * star ω *
        ((tetraB : ℂ) * (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I))) = (1 / 3 : ℝ)
  simpa using normSq_qubit_offdiag_star_omega_mul_explicit_omega_sq

/-- A qubit SIC overlap written with an explicit `starRingEnd` form of $\omega`. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_qubit_offdiag_explicit_omega_exact :
    Complex.normSq ((1 / 3 : ℂ) + (2 / 3 : ℂ) *
      (-(1 : ℂ) / (starRingEnd ℂ) 2 + ((Real.sqrt 3 : ℂ) / (starRingEnd ℂ) 2) * Complex.I)) =
      (1 / 3 : ℝ) := by
  have h :
      (-(1 : ℂ) / (starRingEnd ℂ) 2 + ((Real.sqrt 3 : ℂ) / (starRingEnd ℂ) 2) * Complex.I)
        = (-(1 / 2 : ℂ) + ((Real.sqrt 3 : ℂ) / 2) * Complex.I) := by
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
      change star (2 : ℂ) = 2
      simp
    simpa [htwo] using
      (show (-(1 : ℂ) / 2 + ((Real.sqrt 3 : ℂ) / 2) * Complex.I)
          = (-(1 / 2 : ℂ) + ((Real.sqrt 3 : ℂ) / 2) * Complex.I) by
        norm_num)
  rw [h]
  exact normSq_qubit_offdiag_explicit_omega

/-- A qubit SIC overlap with an explicit `starRingEnd` form and an extra factor of $\omega`. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_qubit_offdiag_tetraB_explicit_omega_mul_omega_exact :
    Complex.normSq ((1 / 3 : ℂ) +
      (tetraB : ℂ) *
        (-(1 : ℂ) / (starRingEnd ℂ) 2 + ((Real.sqrt 3 : ℂ) / (starRingEnd ℂ) 2) * Complex.I) *
        ((tetraB : ℂ) * ω)) = (1 / 3 : ℝ) := by
  have h :
      (-(1 : ℂ) / (starRingEnd ℂ) 2 + ((Real.sqrt 3 : ℂ) / (starRingEnd ℂ) 2) * Complex.I)
        = (-(1 / 2 : ℂ) + ((Real.sqrt 3 : ℂ) / 2) * Complex.I) := by
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
      change star (2 : ℂ) = 2
      simp
    simpa [htwo] using
      (show (-(1 : ℂ) / 2 + ((Real.sqrt 3 : ℂ) / 2) * Complex.I)
          = (-(1 / 2 : ℂ) + ((Real.sqrt 3 : ℂ) / 2) * Complex.I) by
        norm_num)
  rw [h]
  exact normSq_qubit_offdiag_tetraB_explicit_omega_mul_omega

/-- A qubit SIC overlap written with the explicit closed form for $\omega^2$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_qubit_offdiag_explicit_omega_sq :
    Complex.normSq ((1 / 3 : ℂ) + (2 / 3 : ℂ) *
      (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I)) = (1 / 3 : ℝ) := by
  rw [explicit_neg_half_sub_sqrt_three_half_mul_I_eq_omega_sq]
  simpa using normSq_qubit_offdiag_omega_sq

/-- The same explicit $\omega^2$ overlap with the scalar on the left. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_qubit_offdiag_explicit_omega_sq_left :
    Complex.normSq ((1 / 3 : ℂ) +
      (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I) * (2 / 3 : ℂ)) = (1 / 3 : ℝ) := by
  simpa [mul_comm] using normSq_qubit_offdiag_explicit_omega_sq

/-- The complex norm-squared of $1/2$ is $1/4$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_half : Complex.normSq ((1 / 2 : ℂ)) = (1 / 4 : ℝ) := by
  norm_num [Complex.normSq_ofReal]

/-- The complex norm-squared of $-1/2$ is $1/4$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_neg_half : Complex.normSq (-(1 / 2 : ℂ)) = (1 / 4 : ℝ) := by
  rw [Complex.normSq_neg]
  simpa using normSq_half

/-- The complex norm-squared of $(1/2)\omega$ is $1/4$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_half_mul_omega : Complex.normSq (((1 / 2 : ℂ)) * ω) = (1 / 4 : ℝ) := by
  rw [Complex.normSq_mul, omega_normSq]
  norm_num [Complex.normSq_ofReal]

/-- The complex norm-squared of $(1/2)\omega^2$ is $1/4$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_half_mul_omega_sq : Complex.normSq (((1 / 2 : ℂ)) * (ω ^ 2)) = (1 / 4 : ℝ) := by
  rw [Complex.normSq_mul, omega_sq_normSq]
  norm_num [Complex.normSq_ofReal]

/-- The complex norm-squared of $(1/2)(1 + \omega)$ is $1/4$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_half_mul_one_add_omega : Complex.normSq (((1 / 2 : ℂ)) * (1 + ω)) = (1 / 4 : ℝ) := by
  rw [Complex.normSq_mul, normSq_one_add_omega]
  norm_num [Complex.normSq_ofReal]

/-- The complex norm-squared of $(1/2)(1 + \omega^2)$ is $1/4$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_half_mul_one_add_omega_sq :
    Complex.normSq (((1 / 2 : ℂ)) * (1 + ω ^ 2)) = (1 / 4 : ℝ) := by
  rw [Complex.normSq_mul, normSq_one_add_omega_sq]
  norm_num [Complex.normSq_ofReal]

/-- The complex norm-squared of $1/2 + (1/2)\omega$ is $1/4$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_half_add_half_mul_omega :
    Complex.normSq (((1 / 2 : ℂ)) + ((1 / 2 : ℂ)) * ω) = (1 / 4 : ℝ) := by
  have h : (((1 / 2 : ℂ)) + ((1 / 2 : ℂ)) * ω) = (((1 / 2 : ℂ)) * (1 + ω)) := by
    ring
  rw [h]
  simpa using normSq_half_mul_one_add_omega

/-- The complex norm-squared of $1/2 + (1/2)\omega^2$ is $1/4$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_half_add_half_mul_omega_sq :
    Complex.normSq (((1 / 2 : ℂ)) + ((1 / 2 : ℂ)) * (ω ^ 2)) = (1 / 4 : ℝ) := by
  have h : (((1 / 2 : ℂ)) + ((1 / 2 : ℂ)) * (ω ^ 2)) = (((1 / 2 : ℂ)) * (1 + ω ^ 2)) := by
    ring
  rw [h]
  simpa using normSq_half_mul_one_add_omega_sq

/-- The complex norm-squared of $1/2 + (1/2)\omega^2$ in explicit form is $1/4$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_half_add_half_mul_explicit_omega_sq :
    Complex.normSq (((1 / 2 : ℂ)) + ((1 / 2 : ℂ)) *
      (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I)) = (1 / 4 : ℝ) := by
  rw [explicit_neg_half_sub_sqrt_three_half_mul_I_eq_omega_sq]
  simpa using normSq_half_add_half_mul_omega_sq

/-- The complex norm-squared of $(1/2)\omega^2 + 1/2$ in explicit form is $1/4$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_half_mul_explicit_omega_sq_add_half :
    Complex.normSq (((1 / 2 : ℂ)) *
      (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I) + ((1 / 2 : ℂ))) = (1 / 4 : ℝ) := by
  simpa [add_comm, mul_comm] using normSq_half_add_half_mul_explicit_omega_sq

/-- The complex norm-squared of $-(1/2)\omega$ is $1/4$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_neg_half_mul_omega : Complex.normSq (-(((1 / 2 : ℂ)) * ω)) = (1 / 4 : ℝ) := by
  rw [Complex.normSq_neg]
  simpa using normSq_half_mul_omega

/-- The complex norm-squared of $-(1/2)\omega^2$ is $1/4$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_neg_half_mul_omega_sq : Complex.normSq (-(((1 / 2 : ℂ)) * (ω ^ 2))) = (1 / 4 : ℝ) := by
  rw [Complex.normSq_neg]
  simpa using normSq_half_mul_omega_sq

/-- The complex norm-squared of $-(1/2)(1 + \omega)$ is $1/4$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_neg_half_mul_one_add_omega :
    Complex.normSq (-(((1 / 2 : ℂ)) * (1 + ω))) = (1 / 4 : ℝ) := by
  rw [Complex.normSq_neg]
  simpa using normSq_half_mul_one_add_omega

/-- The complex norm-squared of $-(1/2)(1 + \omega^2)$ is $1/4$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_neg_half_mul_one_add_omega_sq :
    Complex.normSq (-(((1 / 2 : ℂ)) * (1 + ω ^ 2))) = (1 / 4 : ℝ) := by
  rw [Complex.normSq_neg]
  simpa using normSq_half_mul_one_add_omega_sq

/-- The explicit $-\tfrac12 + \tfrac{\sqrt3}{2}i$ expression has norm-squared $1$. -/
@[simp, category API, AMS 15 47 81]
lemma explicit_neg_half_add_sqrt_three_half_mul_I_normSq :
    Complex.normSq (-(1 / 2 : ℂ) + ((Real.sqrt 3 : ℂ) / 2) * Complex.I) = 1 := by
  have h :
      (-(1 / 2 : ℂ) + ((Real.sqrt 3 : ℂ) / 2) * Complex.I)
        = (-(1 / 2 : ℂ) + Complex.I * ((Real.sqrt 3 : ℂ) / 2)) := by
    ring
  rw [h, explicit_neg_half_add_I_mul_sqrt_three_half_eq_omega]
  simp

/-- An explicit `starRingEnd` form of $\omega`. -/
@[category API, AMS 15 47 81]
lemma explicit_omega_fin_eq :
    (-(1 : ℂ) / (starRingEnd ℂ) 2 + ((Real.sqrt 3 : ℂ) / (starRingEnd ℂ) 2) * Complex.I)
      = (-(1 / 2 : ℂ) + ((Real.sqrt 3 : ℂ) / 2) * Complex.I) := by
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    change star (2 : ℂ) = 2
    simp
  simpa [htwo] using
    (show (-(1 : ℂ) / 2 + ((Real.sqrt 3 : ℂ) / 2) * Complex.I)
        = (-(1 / 2 : ℂ) + ((Real.sqrt 3 : ℂ) / 2) * Complex.I) by
      norm_num)

/-- The explicit `starRingEnd` form of $\omega` has norm-squared $1$. -/
@[simp, category API, AMS 15 47 81]
lemma explicit_omega_fin_normSq :
    Complex.normSq
      (-(1 : ℂ) / (starRingEnd ℂ) 2 + ((Real.sqrt 3 : ℂ) / (starRingEnd ℂ) 2) * Complex.I) = 1 := by
  rw [explicit_omega_fin_eq]
  exact explicit_neg_half_add_sqrt_three_half_mul_I_normSq

/-- The complex norm-squared of $1/2 + (1/2)\overline{\omega}$ is $1/4$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_half_add_half_mul_star_omega_fin :
    Complex.normSq ((1 / 2 : ℂ) + (1 / 2 : ℂ) * (starRingEnd ℂ) ω) = (1 / 4 : ℝ) := by
  change Complex.normSq ((1 / 2 : ℂ) + (1 / 2 : ℂ) * star ω) = (1 / 4 : ℝ)
  rw [star_omega]
  simpa using normSq_half_add_half_mul_omega_sq

/-- A Hesse-family overlap written using `starRingEnd` and the explicit $\omega^2$ form. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_half_add_hesseS_star_omega_mul_hesseS_explicit_omega_sq_fin :
    Complex.normSq ((1 / 2 : ℂ) +
      (hesseS : ℂ) * (starRingEnd ℂ) ω *
        ((hesseS : ℂ) * (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I))) = (1 / 4 : ℝ) := by
  change Complex.normSq ((1 / 2 : ℂ) +
      (hesseS : ℂ) * star ω *
        ((hesseS : ℂ) * (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I))) = (1 / 4 : ℝ)
  rw [star_omega, explicit_neg_half_sub_sqrt_three_half_mul_I_eq_omega_sq]
  ring_nf
  simpa only [pow_two, hesseS_sq_complex, omega_four] using normSq_half_add_half_mul_omega

/-- The complex norm-squared of $(1/2)\omega + 1/2$ is $1/4$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_half_mul_omega_add_half :
    Complex.normSq (((1 / 2 : ℂ) * ω) + (1 / 2 : ℂ)) = (1 / 4 : ℝ) := by
  simpa [add_comm, mul_comm] using normSq_half_add_half_mul_omega

/-- The complex norm-squared of $(1/2)\overline{\omega} + 1/2$ is $1/4$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_half_mul_star_omega_add_half_fin :
    Complex.normSq (((1 / 2 : ℂ) * (starRingEnd ℂ) ω) + (1 / 2 : ℂ)) = (1 / 4 : ℝ) := by
  simpa [add_comm, mul_comm] using normSq_half_add_half_mul_star_omega_fin

/-- A Hesse-family overlap written as $\overline{\omega}$ times the explicit $\omega^2$ form plus $1/2$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_hesse_star_omega_mul_hesseS_explicit_omega_sq_add_half_fin :
    Complex.normSq
      ((hesseS : ℂ) * (starRingEnd ℂ) ω *
        ((hesseS : ℂ) * (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I)) + (1 / 2 : ℂ)) =
      (1 / 4 : ℝ) := by
  simpa [add_comm] using normSq_half_add_hesseS_star_omega_mul_hesseS_explicit_omega_sq_fin

/-- The complex norm-squared of $1/2 + (1/2)\omega$ in explicit `starRingEnd` form is $1/4$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_half_add_half_mul_explicit_omega_fin :
    Complex.normSq ((1 / 2 : ℂ) +
      (1 / 2 : ℂ) *
        (-(1 : ℂ) / (starRingEnd ℂ) 2 + ((Real.sqrt 3 : ℂ) / (starRingEnd ℂ) 2) * Complex.I)) =
      (1 / 4 : ℝ) := by
  rw [explicit_omega_fin_eq]
  have h :
      (-(1 / 2 : ℂ) + ((Real.sqrt 3 : ℂ) / 2) * Complex.I)
        = (-(1 / 2 : ℂ) + Complex.I * ((Real.sqrt 3 : ℂ) / 2)) := by
    ring
  rw [h, explicit_neg_half_add_I_mul_sqrt_three_half_eq_omega]
  simpa using normSq_half_add_half_mul_omega

/-- A Hesse-family overlap written using the explicit `starRingEnd` form of $\omega`. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_half_add_hesseS_explicit_omega_mul_hesseS_omega_fin :
    Complex.normSq ((1 / 2 : ℂ) +
      (hesseS : ℂ) *
        (-(1 : ℂ) / (starRingEnd ℂ) 2 + ((Real.sqrt 3 : ℂ) / (starRingEnd ℂ) 2) * Complex.I) *
        ((hesseS : ℂ) * ω)) = (1 / 4 : ℝ) := by
  rw [explicit_omega_fin_eq]
  have h :
      (-(1 / 2 : ℂ) + ((Real.sqrt 3 : ℂ) / 2) * Complex.I)
        = (-(1 / 2 : ℂ) + Complex.I * ((Real.sqrt 3 : ℂ) / 2)) := by
    ring
  rw [h, explicit_neg_half_add_I_mul_sqrt_three_half_eq_omega]
  ring_nf
  simpa only [pow_two, hesseS_sq_complex] using normSq_half_add_half_mul_omega_sq

/-- The complex norm-squared of the explicit `starRingEnd` form of $(1/2)\omega + 1/2$ is $1/4$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_half_mul_explicit_omega_add_half_fin :
    Complex.normSq
      (((1 / 2 : ℂ) *
        (-(1 : ℂ) / (starRingEnd ℂ) 2 + ((Real.sqrt 3 : ℂ) / (starRingEnd ℂ) 2) * Complex.I)) +
        (1 / 2 : ℂ)) = (1 / 4 : ℝ) := by
  simpa [add_comm, mul_comm] using normSq_half_add_half_mul_explicit_omega_fin

/-- A Hesse-family overlap written using the explicit `starRingEnd` form of $\omega` plus $1/2$. -/
@[simp, category test, AMS 15 47 81]
lemma normSq_hesse_explicit_omega_mul_hesseS_omega_add_half_fin :
    Complex.normSq
      ((hesseS : ℂ) *
        (-(1 : ℂ) / (starRingEnd ℂ) 2 + ((Real.sqrt 3 : ℂ) / (starRingEnd ℂ) 2) * Complex.I) *
        ((hesseS : ℂ) * ω) + (1 / 2 : ℂ)) = (1 / 4 : ℝ) := by
  simpa [add_comm] using normSq_half_add_hesseS_explicit_omega_mul_hesseS_omega_fin

/-- The tetrahedral qubit SIC family. -/
def qubitSICFamily : Fin 4 → StateVector 2
  | 0 => vec2 1 0
  | 1 => vec2 (tetraA : ℂ) (tetraB : ℂ)
  | 2 => vec2 (tetraA : ℂ) ((tetraB : ℂ) * ω)
  | _ => vec2 (tetraA : ℂ) ((tetraB : ℂ) * (ω ^ 2))

/-- The Hesse qutrit SIC family. -/
def hesseFamily : Fin 9 → StateVector 3
  | 0 => vec3 0 (hesseS : ℂ) (-(hesseS : ℂ))
  | 1 => vec3 0 (hesseS : ℂ) (-((hesseS : ℂ) * ω))
  | 2 => vec3 0 (hesseS : ℂ) (-((hesseS : ℂ) * (ω ^ 2)))
  | 3 => vec3 (-(hesseS : ℂ)) 0 (hesseS : ℂ)
  | 4 => vec3 (-((hesseS : ℂ) * ω)) 0 (hesseS : ℂ)
  | 5 => vec3 (-((hesseS : ℂ) * (ω ^ 2))) 0 (hesseS : ℂ)
  | 6 => vec3 (hesseS : ℂ) (-(hesseS : ℂ)) 0
  | 7 => vec3 (hesseS : ℂ) (-((hesseS : ℂ) * ω)) 0
  | _ => vec3 (hesseS : ℂ) (-((hesseS : ℂ) * (ω ^ 2))) 0

/-- The BB84 family of four qubit states. -/
def bb84Family : Fin 4 → StateVector 2
  | 0 => vec2 1 0
  | 1 => vec2 0 1
  | 2 => vec2 (hesseS : ℂ) (hesseS : ℂ)
  | _ => vec2 (hesseS : ℂ) (-(hesseS : ℂ))

/-- The SIC overlap value in dimension $2$ is $1/3$. -/
@[category test, AMS 15 47 81]
lemma sicOverlapSq_two : sicOverlapSq 2 = (1 / 3 : ℝ) := by
  norm_num [sicOverlapSq]

/-- The SIC overlap value in dimension $3$ is $1/4$. -/
@[category test, AMS 15 47 81]
lemma sicOverlapSq_three : sicOverlapSq 3 = (1 / 4 : ℝ) := by
  norm_num [sicOverlapSq]

/-- Every vector in the tetrahedral qubit SIC family is normalized. -/
@[category test, AMS 15 47 81]
lemma qubitSICFamily_normalized (i : Fin 4) : IsNormalized (qubitSICFamily i) := by
  fin_cases i
  all_goals
    apply isNormalized_of_coord_normSq_sum_one
    simp [qubitSICFamily, vec2, Fin.sum_univ_two]
    try norm_num

/-- The tetrahedral qubit SIC family has the correct constant pairwise overlap. -/
@[category test, AMS 15 47 81]
lemma qubitSICFamily_pairwise : HasConstantOverlapSq (sicOverlapSq 2) qubitSICFamily := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  interval_cases i <;> interval_cases j
  all_goals
    simp [qubitSICFamily, vec2, overlapSq, sicOverlapSq, Fin.sum_univ_two] at hij ⊢
    first
      | done
      | contradiction
      | norm_num [sicOverlapSq]

/-- Dimension $2$ admits a SIC-POVM, witnessed by the tetrahedral qubit SIC. -/
@[category test, AMS 15 47 81]
theorem hasSICPOVM_two : HasSICPOVM 2 := by
  refine ⟨qubitSICFamily, ?_⟩
  constructor
  · intro i
    exact qubitSICFamily_normalized i
  · exact qubitSICFamily_pairwise

/-- Every vector in the Hesse qutrit SIC family is normalized. -/
@[category test, AMS 15 47 81]
lemma hesseFamily_normalized (i : Fin 9) : IsNormalized (hesseFamily i) := by
  fin_cases i
  all_goals
    apply isNormalized_of_coord_normSq_sum_one
    simp [hesseFamily, vec3, Fin.sum_univ_three]
    try norm_num

set_option maxHeartbeats 1000000 in
/-- The Hesse qutrit SIC family has the correct constant pairwise overlap. -/
@[category test, AMS 15 47 81]
lemma hesseFamily_pairwise : HasConstantOverlapSq (sicOverlapSq 3) hesseFamily := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  interval_cases i <;> interval_cases j
  all_goals
    simp [hesseFamily, vec3, overlapSq, sicOverlapSq, Fin.sum_univ_three] at hij ⊢
    first
      | done
      | contradiction
      | norm_num [sicOverlapSq]

/-- Dimension $3$ admits a SIC-POVM, witnessed by the Hesse qutrit SIC. -/
@[category test, AMS 15 47 81]
theorem hasSICPOVM_three : HasSICPOVM 3 := by
  refine ⟨hesseFamily, ?_⟩
  constructor
  · intro i
    exact hesseFamily_normalized i
  · exact hesseFamily_pairwise

/-- Every vector in the BB84 family is normalized. -/
@[category test, AMS 15 47 81]
lemma bb84Family_normalized (i : Fin 4) : IsNormalized (bb84Family i) := by
  fin_cases i
  all_goals
    apply isNormalized_of_coord_normSq_sum_one
    simp [bb84Family, vec2, Fin.sum_univ_two]
    try norm_num

/-- The BB84 family has the right cardinality for a qubit SIC but fails the constant-overlap condition. -/
@[category test, AMS 15 47 81]
theorem bb84Family_not_isSICFamily : ¬ IsSICFamily 2 bb84Family := by
  intro h
  have h01 : overlapSq (bb84Family 0) (bb84Family 1) = sicOverlapSq 2 := by
    exact h.2 (by decide : (0 : Fin 4) ≠ 1)
  have hoff : overlapSq (bb84Family 0) (bb84Family 1) = 0 := by
    simp [bb84Family, vec2, overlapSq, Fin.sum_univ_two]
  have hsic : sicOverlapSq 2 = (1 / 3 : ℝ) := by
    norm_num [sicOverlapSq]
  nlinarith [h01, hoff, hsic]

/- ## Smallest open special cases (all d<=75) -/

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $56$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_56 : answer(sorry) ↔ HasSICPOVM 56 := by
  sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $58$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_58 : answer(sorry) ↔ HasSICPOVM 58 := by
  sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $59$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_59 : answer(sorry) ↔ HasSICPOVM 59 := by
  sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $60$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_60 : answer(sorry) ↔ HasSICPOVM 60 := by
  sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $64$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_64 : answer(sorry) ↔ HasSICPOVM 64 := by
  sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $68$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_68 : answer(sorry) ↔ HasSICPOVM 68 := by
  sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $69$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_69 : answer(sorry) ↔ HasSICPOVM 69 := by
  sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $70$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_70 : answer(sorry) ↔ HasSICPOVM 70 := by
  sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $71$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_71 : answer(sorry) ↔ HasSICPOVM 71 := by
  sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $72$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_72 : answer(sorry) ↔ HasSICPOVM 72 := by
  sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $75$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_75 : answer(sorry) ↔ HasSICPOVM 75 := by
  sorry

/- ## Full conjecture -/

/-- Do SIC-POVMs exist in every finite dimension? -/
@[category research open, AMS 15 47 81]
theorem sicPOVMs :
    answer(sorry) ↔ ∀ d : ℕ, 1 ≤ d → HasSICPOVM d := by
  sorry

end OpenQuantumProblem23
