/-
Copyright 2025 Google LLC

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

--Wikipedia URL: https://en.wikipedia.org/wiki/Schanuel%27s_conjecture
import FormalConjectures.Util.ProblemImports

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
@[problem_status solved]
theorem isTranscendenceBasis_ncard_eq_transcendenceDegree (R : Type*) {A ι : Type*}
    [CommRing R] [CommRing A] [Algebra R A] (h : Function.Injective (algebraMap R A))
    (𝒷 : ι → A) (hS : IsTranscendenceBasis R 𝒷) :
    (Set.univ : Set ι).ncard = transcendenceDegree R h :=
  sorry

open IntermediateField in
/--
If the transcendence degree of $A$ adjoined $\{x_1, ..., x_n\}$ is $\leq n$.
-/
@[problem_status solved]
theorem adjoin_transcendenceDegree_le_of_finite {A ι : Type*} [Field A] {S : Set A}
    (hS : S.Finite) :
    transcendenceDegree A (algebraMap A (adjoin A S)).injective ≤ S.ncard :=
  sorry

open IntermediateField in
/--
Given any set of $n$ complex numbers $\{z_1, ..., z_n\}$ that are linearly
independent over $\mathbb{Q}$, the field extension
$\mathbb{Q}(z_1, ..., z_n, e^{z_1}, ..., e^{z_n})$ has transcendence degree
at least $n$ over $\mathbb{Q}$.
-/
@[problem_status open]
theorem schanuels_conjecture (n : ℕ) (z : Fin n → ℂ)
    (h : LinearIndependent ℚ z) :
    let hinj := algebraMap ℚ (adjoin ℚ (Set.range z ∪ Set.range (cexp ∘ z))) |>.injective
    n ≤ transcendenceDegree ℚ hinj := sorry

/-! ## Consequences of Schanuel's conjecture -/

/--
The four exponentials conjecture would follow from Schanuel's conjecture: if $z_2, z_2$ and
$w_1, w_2$ are two pairs of complex numbers, with each pair being linearly independent over
the rational numbers, then at least one of the following four numbers is transcendental
$$
  e^{z_1w_1}, e^{z_1w_2}, e^{z_2w_1}, e^{z_2w_2}.
$$
-/
@[problem_status open]
theorem four_exponentials {z₁ z₂ w₁ w₂ : ℂ} (hz : LinearIndependent ℚ ![z₁, z₂])
    (hw : LinearIndependent ℚ ![w₁, w₂]) :
    ∃ z ∈ ({cexp (z₁ * w₁), cexp (z₁ * w₂), cexp (z₂ * w₁), cexp (z₂ * w₂)} : Set ℂ), Transcendental ℚ z :=
  sorry

/--
The four exponential conjecture would imply that for any irrational number $t$, at least one of the numbers
$2^t$ and $3^t$ is transcendental.
-/
@[problem_status open]
theorem exists_transcendental_of_two_pow_irrat_three_pow_irrat {t : ℝ} (h : Irrational t) : Irrational (2 ^ t) ∨ Irrational (3 ^ t) :=
  sorry

/-! A number of nontrivial combinations of $e$, $\pi$ and elementary functions may
also be proven to the transcendental should Schanuel's conjecture hold. -/

/-- $e + \pi$ is transcendental. -/
@[problem_status open]
theorem exp_add_pi_transcendental : Transcendental ℚ (rexp 1 + π) := sorry

/-- $e\pi$ is transcendental. -/
@[problem_status open]
theorem exp_mul_pi_transcendental : Transcendental ℚ (rexp 1 * π) := sorry

/-- $e^{\pi^2}$ is transcendental. -/
@[problem_status open]
theorem exp_pow_pi_sq_transcendental : Transcendental ℚ (rexp (π ^ 2)) := sorry

/-- $e^e$ is transcendental. -/
@[problem_status open]
theorem exp_exp_transcendental : Transcendental ℚ (rexp (rexp 1)) := sorry

/-- $\pi^e$ is transcendental. -/
@[problem_status open]
theorem pi_pow_exp_transcendental : Transcendental ℚ (π ^ (rexp 1)) := sorry

/-- $\pi^{\sqrt{2}}$ is transcendental. -/
@[problem_status open]
theorem pi_pow_sqrt_two_transcendental : Transcendental ℚ (π ^ √2) := sorry

/-- $\pi^{\pi}$ is transcendental. -/
@[problem_status open]
theorem pi_pow_pi_transcendental : Transcendental ℚ (π ^ π) := sorry

/-- $\pi^{\pi^{\pi}}$ is transcendental. -/
@[problem_status open]
theorem pi_pow_pi_pow_pi_transcendental : Transcendental ℚ (π ^ (π ^ π)) := sorry

/-- $\log(\pi)$ is transcendental. -/
@[problem_status open]
theorem rlog_pi_transcendental : Transcendental ℚ (Real.log π) := sorry

/-- $\log(\log(2))$ is transcendental. -/
@[problem_status open]
theorem rlog_rlog_two_transcendental : Transcendental ℚ ((2 : ℝ).log.log) := sorry

/-- $\sin(e)$ is transcendental. -/
@[problem_status open]
theorem sin_exp_transcendental : Transcendental ℚ (Real.sin (rexp 1)) := sorry

/-- At least one of $\pi + e$ and $\pi e$ is transcendental. -/
@[problem_status solved]
theorem exp_add_pi_or_exp_add_mul_transcendental :
    Transcendental ℚ (π + rexp 1) ∨ Transcendental ℚ (π * rexp 1) :=
  sorry
