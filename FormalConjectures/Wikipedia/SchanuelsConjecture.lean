/-
Copyright 2025 The Formal Conjectures Authors.

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

/-!
# Schanuel's Conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Schanuel%27s_conjecture)
-/
open scoped Real Complex

noncomputable section

/--
The transcendence degree of an $A$-algebra is the common cardinality of
transcendence bases.
-/
abbrev transcendenceDegree (R : Type*) {A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (h : Function.Injective (algebraMap R A)) : ℕ :=
    let ι := (exists_isTranscendenceBasis' R h).choose
    (Set.univ : Set ι).ncard

/--
The transcendence degree is independent of the choice of a transcendence basis.
-/
@[category graduate, AMS 12, AMS 13, AMS 14]
theorem isTranscendenceBasis_ncard_eq_transcendenceDegree (R : Type*) {A ι : Type*}
    [CommRing R] [CommRing A] [Algebra R A] (h : Function.Injective (algebraMap R A))
    (𝒷 : ι → A) (hS : IsTranscendenceBasis R 𝒷) :
    (Set.univ : Set ι).ncard = transcendenceDegree R h := by
  sorry

open IntermediateField in
/--
The transcendence degree of $A$ adjoined $\{x_1, ..., x_n\}$ is $\leq n$.
-/
@[category graduate, AMS 12, AMS 13, AMS 14]
theorem adjoin_transcendenceDegree_le_of_finite {A ι : Type*} [Field A] {S : Set A}
    (hS : S.Finite) :
    transcendenceDegree A (algebraMap A (adjoin A S)).injective ≤ S.ncard := by
  sorry

open IntermediateField in
/--
Given any set of $n$ complex numbers $\{z_1, ..., z_n\}$ that are linearly
independent over $\mathbb{Q}$, the field extension
$\mathbb{Q}(z_1, ..., z_n, e^{z_1}, ..., e^{z_n})$ has transcendence degree
at least $n$ over $\mathbb{Q}$.
-/
@[category research open]
theorem schanuels_conjecture (n : ℕ) (z : Fin n → ℂ)
    (h : LinearIndependent ℚ z) :
    let hinj := algebraMap ℚ (adjoin ℚ (Set.range z ∪ Set.range (cexp ∘ z))) |>.injective
    n ≤ transcendenceDegree ℚ hinj := by
  sorry

/-! ## Consequences of Schanuel's conjecture -/

/--
The four exponentials conjecture would follow from Schanuel's conjecture: if $z_2, z_2$ and
$w_1, w_2$ are two pairs of complex numbers, with each pair being linearly independent over
the rational numbers, then at least one of the following four numbers is transcendental
$$
  e^{z_1w_1}, e^{z_1w_2}, e^{z_2w_1}, e^{z_2w_2}.
$$
-/
@[category research open, AMS 11, AMS 33]
theorem four_exponentials {z₁ z₂ w₁ w₂ : ℂ} (hz : LinearIndependent ℚ ![z₁, z₂])
    (hw : LinearIndependent ℚ ![w₁, w₂]) :
    ∃ z ∈ ({cexp (z₁ * w₁), cexp (z₁ * w₂),
      cexp (z₂ * w₁), cexp (z₂ * w₂)} : Set ℂ), Transcendental ℚ z := by
  sorry

/--
The four exponential conjecture would imply that for any irrational number $t$, at least one of the numbers
$2^t$ and $3^t$ is transcendental.
-/
@[category research open, AMS 11]
theorem exists_transcendental_of_two_pow_irrat_three_pow_irrat
    {t : ℝ} (h : Irrational t) : Irrational (2 ^ t) ∨ Irrational (3 ^ t) := by
  sorry

/-! A number of nontrivial combinations of $e$, $\pi$ and elementary functions may
also be proven to the transcendental should Schanuel's conjecture hold. -/

/-- $e + \pi$ is transcendental. -/
@[category research open, AMS 11, AMS 33]
theorem exp_add_pi_transcendental : Transcendental ℚ (rexp 1 + π) := by
  sorry

/-- $e\pi$ is transcendental. -/
@[category research open, AMS 11, AMS 33]
theorem exp_mul_pi_transcendental : Transcendental ℚ (rexp 1 * π) := by
  sorry

/-- $e^{\pi^2}$ is transcendental. -/
@[category research open, AMS 11, AMS 33]
theorem exp_pow_pi_sq_transcendental : Transcendental ℚ (rexp (π ^ 2)) := by
  sorry

/-- $e^e$ is transcendental. -/
@[category research open, AMS 11, AMS 33]
theorem exp_exp_transcendental : Transcendental ℚ (rexp (rexp 1)) := by
  sorry

/-- $\pi^e$ is transcendental. -/
@[category research open, AMS 11, AMS 33]
theorem pi_pow_exp_transcendental : Transcendental ℚ (π ^ (rexp 1)) := by
  sorry

/-- $\pi^{\sqrt{2}}$ is transcendental. -/
@[category research open, AMS 11, AMS 33]
theorem pi_pow_sqrt_two_transcendental : Transcendental ℚ (π ^ √2) := by
  sorry

/-- $\pi^{\pi}$ is transcendental. -/
@[category research open, AMS 11, AMS 33]
theorem pi_pow_pi_transcendental : Transcendental ℚ (π ^ π) := by
  sorry

/-- $\pi^{\pi^{\pi}}$ is transcendental. -/
@[category research open, AMS 11, AMS 33]
theorem pi_pow_pi_pow_pi_transcendental : Transcendental ℚ (π ^ (π ^ π)) := by
  sorry

/-- $\log(\pi)$ is transcendental. -/
@[category research open, AMS 11, AMS 33]
theorem rlog_pi_transcendental : Transcendental ℚ (Real.log π) := by
  sorry

/-- $\log(\log(2))$ is transcendental. -/
@[category research open, AMS 11, AMS 33]
theorem rlog_rlog_two_transcendental : Transcendental ℚ ((2 : ℝ).log.log) := by
  sorry

/-- $\sin(e)$ is transcendental. -/
@[category research open, AMS 11, AMS 33]
theorem sin_exp_transcendental : Transcendental ℚ (Real.sin (rexp 1)) := by
  sorry

/-- At least one of $\pi + e$ and $\pi e$ is transcendental. -/
@[category undergraduate, AMS 11]
theorem exp_add_pi_or_exp_add_mul_transcendental :
    Transcendental ℚ (π + rexp 1) ∨ Transcendental ℚ (π * rexp 1) :=
  sorry
