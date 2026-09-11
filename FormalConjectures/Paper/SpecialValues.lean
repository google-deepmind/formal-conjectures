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
import FormalConjecturesUtil

/-!
# Special values of $L$-functions

*References:*
- [De79] P. Deligne, *Valeurs de fonctions L et périodes d'intégrales*, in Automorphic Forms,
  Representations and L-functions (Corvallis 1977), Proc. Sympos. Pure Math. 33, Part 2,
  AMS (1979), 313-346. States the conjecture (Conj. 2.8) and the critical integers (§1.3);
  the Dirichlet character case is §6.
- [Wa97] L. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Springer (1997),
  Ch. 4. Generalized Bernoulli numbers and the values at non-positive integers.
- [Ne99] J. Neukirch, Algebraic Number Theory, Springer (1999), Ch. VII §2. The Gamma factor
  of a Dirichlet L-function, with shift 0 or 1 according to the parity of the character.
-/

namespace Deligne

open Complex ZMod

/-- A Deligne package with respect to a parameter `M : Ω` is the tuple `(L, E, w, γ, c, σ)` where
- `L` : L-function;
- `E` : algebraic subfield of ℂ containing L-values;
- `w` : weight with respect to which the functional equation of `L` is expressed;
- `γ` : gamma factors of the completed L-function;
- `c` : period;
- `σ` : Galois action on `M`.
This contains the data required to state Deligne's conjecture for `M`. While Deligne's conjecture
is traditionally stated for motives in the literature, we lack a formal definition of a motive.
Moreover, this allows one to state the conjecture in potentially non-motivic cases. -/
structure Pkg (Ω : Type*) where
  /-- The analytic `L`-function `L(M, s)`. -/
  L : Ω → ℂ → ℂ
  /-- The value field `E(M)`. -/
  valueField : Ω → IntermediateField ℚ ℂ
  /-- The weight `w(M)`: the functional equation exchanges `s` and `w(M) + 1 - s`. -/
  weight : Ω → ℤ
  /-- The shifts of the archimedean Gamma factor, `∏ a, Γℝ(s + a)` with `a` ranging over
  `gammaShifts M` with multiplicity. -/
  gammaShifts : Ω → Multiset ℤ
  /-- Deligne's period `c⁺(M(n))`. -/
  period : Ω → ℤ → ℂ
  /-- The Galois action `σ ↦ (M ↦ Mᵟ)`. -/
  galoisAction : Gal(ℂ/ℚ) →* Equiv.Perm Ω
  /-- Conjugate inputs have the same weight. -/
  weight_galoisAction (σ : Gal(ℂ/ℚ)) (M : Ω) : weight (galoisAction σ M) = weight M
  /-- Conjugate inputs have the same Hodge numbers. -/
  gammaShifts_galoisAction (σ : Gal(ℂ/ℚ)) (M : Ω) :
    gammaShifts (galoisAction σ M) = gammaShifts M
  /-- The coefficient field transports along the action. -/
  valueField_galoisAction (σ : Gal(ℂ/ℚ)) (M : Ω) :
    valueField (galoisAction σ M) = (valueField M).map σ
  /-- The coefficient field is algebraic over `ℚ`. -/
  valueField_isAlgebraic (M : Ω) {x : ℂ} (hx : x ∈ valueField M) : IsAlgebraic ℚ x
  /-- Prevents trivial junk case `· / 0 = 0 ∈ valueField`. -/
  period_ne_zero' (M : Ω) (n : ℤ)
    (h₁ : ∀ a ∈ gammaShifts M, Odd (n + a) ∨ 0 < n + a)
    (h₂ : ∀ a ∈ gammaShifts M, Odd (weight M + 1 - n + a) ∨ 0 < weight M + 1 - n + a) :
    period M n ≠ 0

namespace Pkg

variable {Ω : Type*} {F : Pkg Ω}

/-- The gamma factor of the package is the product of `Γ(s + a)`, where `a` are given by the
multiset of integer shifts defined in the package.-/
noncomputable def gammaFactor (M : Ω) (s : ℂ) : ℂ := prodGammaℝ (F.gammaShifts M) s

/-- An integer `n` is critical for `M` if the gamma factor has pole neither at `n` nor at
`weight + 1 - n`. -/
def IsCritical (M : Ω) (n : ℤ) : Prop :=
  0 ≤ meromorphicOrderAt (F.gammaFactor M) (n : ℂ) ∧
    0 ≤ meromorphicOrderAt (F.gammaFactor M) ((F.weight M + 1 - n : ℤ) : ℂ)

@[category API, AMS 11 14]
lemma isCritical_iff (M : Ω) (n : ℤ) :
    F.IsCritical M n ↔ (∀ a ∈ F.gammaShifts M, Odd (n + a) ∨ 0 < n + a) ∧
      ∀ a ∈ F.gammaShifts M, Odd (F.weight M + 1 - n + a) ∨ 0 < F.weight M + 1 - n + a := by
  have hgf : F.gammaFactor M = prodGammaℝ (F.gammaShifts M) := rfl
  simp only [IsCritical, hgf, meromorphicOrderAt_prodGammaℝ_intCast_nonneg_iff]

@[category API, AMS 11 14]
lemma period_ne_zero (M : Ω) (n : ℤ) (h : F.IsCritical M n) : F.period M n ≠ 0 :=
  F.period_ne_zero' M n ((isCritical_iff M n).1 h).1 ((isCritical_iff M n).1 h).2

/-- The normalised critical value `L(M, n) / c⁺(M, n)`. -/
noncomputable def normalizedValue (M : Ω) (n : ℤ) : ℂ := F.L M n / F.period M n

/-- The package is arithmetic if the normalized critical values are in the value field. -/
def IsArithmetic (M : Ω) : Prop := ∀ (n : ℤ), F.IsCritical M n →
  F.normalizedValue M n ∈ F.valueField M

/-- The packages is equivariant if the normalized critical values are equivariant under the
Galois action. -/
def IsEquivariant (M : Ω) : Prop :=
  ∀ (σ : Gal(ℂ/ℚ)) (n : ℤ), F.IsCritical M n →
    σ (F.normalizedValue M n) = F.normalizedValue (F.galoisAction σ M) n

/-- Deligne's conjecture for `(L, E, w, γ, c, σ)` consists of arithmeticity and
equivariance. -/
abbrev Conjecture (M : Ω) : Prop := F.IsArithmetic M ∧ F.IsEquivariant M

@[category API, AMS 11 14]
lemma isCritical_galoisAction_iff (σ : Gal(ℂ/ℚ)) (M : Ω) (n : ℤ) :
    F.IsCritical (F.galoisAction σ M) n ↔ F.IsCritical M n := by
  simp only [isCritical_iff, gammaShifts_galoisAction, weight_galoisAction]

section trivial_cases

/- Some cases are trivial, either mathematically or by the choice of formalization of `Pkg`. -/


/-- Empty critical set: if `M` has no critical integers, then the formal conjecture is vacuously
true. This occurs in nature, for example the Dedekind zeta function of an imaginary
quadratic field has no critical integers [Ne99]. -/
@[category test, AMS 11 14]
theorem conjecture_of_forall_not_isCritical {F : Pkg Ω} {M : Ω}
    (h : ∀ n : ℤ, ¬ F.IsCritical M n) : F.Conjecture M :=
  ⟨fun n hn ↦ absurd hn (h n), fun _ n hn ↦ absurd hn (h n)⟩

/-- Vanishing L-function: if the L-function vanishes at the critical points on the Galois orbit
of `M`, then the formal conjecture is trivially true. -/
@[category test, AMS 11 14]
theorem conjecture_of_L_eq_zero {F : Pkg Ω} {M : Ω}
    (h : ∀ (σ : Gal(ℂ/ℚ)) (n : ℤ), F.IsCritical M n → F.L (F.galoisAction σ M) n = 0) :
    F.Conjecture M := by
  have hM : ∀ n, F.IsCritical M n → F.L M n = 0 := fun n hn ↦ by simpa using h 1 n hn
  refine ⟨fun n hn ↦ ?_, fun σ n hn ↦ ?_⟩
  · simp [normalizedValue, hM n hn]
  · simp [normalizedValue, hM n hn, h σ n hn]

/-- Trivial period: if on the Galois orbit of `M`, the supplied period is some rescaling of the
`L`-function. at critical integers, then the formal conjecture is trivially true. -/
@[category test, AMS 11 14]
theorem conjecture_of_period_eq_mul_L {F : Pkg Ω} {M : Ω} (e : ℤ → F.valueField M)
    (h : ∀ (σ : Gal(ℂ/ℚ)) (n : ℤ), F.IsCritical M n →
      F.period (F.galoisAction σ M) n = σ (e n) * F.L (F.galoisAction σ M) n) :
    F.Conjecture M := by
  have hL (σ : Gal(ℂ/ℚ)) (n : ℤ) (hn : F.IsCritical M n) :
      F.L (F.galoisAction σ M) n ≠ 0 := right_ne_zero_of_mul <|
    h σ n hn ▸ F.period_ne_zero _ n ((F.isCritical_galoisAction_iff σ M n).2 hn)
  have hval (σ : Gal(ℂ/ℚ)) (n : ℤ) (hn : F.IsCritical M n) :
      F.normalizedValue (F.galoisAction σ M) n = (σ (e n))⁻¹ := by
    rw [normalizedValue, h σ n hn, mul_comm, ← div_div, div_self (hL σ n hn), one_div]
  have hM (n : ℤ) (hn : F.IsCritical M n) : F.normalizedValue M n = (e n : ℂ)⁻¹ := by
    simpa using hval 1 n hn
  exact ⟨fun n hn ↦ hM n hn ▸ inv_mem (e n).2, fun σ n hn ↦ by rw [hM n hn, hval σ n hn, map_inv₀]⟩

end trivial_cases

end Pkg

namespace GL1

variable {N : ℕ} (χ : DirichletCharacter ℂ N)

/-- The field `ℚ(χ)` generated by the values of a Dirichlet character. -/
noncomputable abbrev valueField : IntermediateField ℚ ℂ := .adjoin ℚ (Set.range χ)

/-- The Galois conjugate `χ ^ σ = σ ∘ χ` of a Dirichlet character. -/
noncomputable abbrev galoisConj (σ : Gal(ℂ/ℚ)) :
    DirichletCharacter ℂ N := χ.ringHomComp (σ : ℂ →+* ℂ)

@[simp, category API, AMS 11 14]
lemma galoisConj_apply (σ : Gal(ℂ/ℚ)) (a : ZMod N) :
    galoisConj χ σ a = σ (χ a) := rfl

@[simp, category API, AMS 11 14]
lemma coe_galoisConj (σ : Gal(ℂ/ℚ)) : ⇑(galoisConj χ σ) = σ ∘ χ := rfl

/-- Galois conjugation preserves the parity of a Dirichlet character: `σ` fixes `1`, so
`χ ^ σ (-1) = 1` exactly when `χ (-1) = 1`. -/
@[simp, category API, AMS 11 14]
lemma even_galoisConj (σ : Gal(ℂ/ℚ)) : (galoisConj χ σ).Even ↔ χ.Even := by
  simp only [DirichletCharacter.Even, galoisConj_apply]
  exact ⟨fun h ↦ σ.injective (by rw [map_one]; exact h), fun h ↦ by rw [h, map_one]⟩

variable {χ} in
@[category API, AMS 11 14]
lemma isPrimitive_galoisConj [NeZero N] (σ : Gal(ℂ/ℚ)) (hχ : χ.IsPrimitive) :
    (galoisConj χ σ).IsPrimitive := hχ.ringHomComp σ.injective

@[category API, AMS 11 14]
lemma valueField_galoisConj (σ : Gal(ℂ/ℚ)) (χ : DirichletCharacter ℂ N) :
    valueField (galoisConj χ σ) = (valueField χ).map σ := by
  rw [valueField, valueField, coe_galoisConj, Set.range_comp, IntermediateField.adjoin_map,
    AlgEquiv.coe_toAlgHom]

/-- Deligne's period `c⁺(M(χ)(n))`: the Gauss sum of `χ` times `(2πi) ^ n` for `n ≥ 1`, and `1`
for `n ≤ 0`. -/
noncomputable def period [NeZero N] (χ : DirichletCharacter ℂ N) (n : ℤ) : ℂ :=
  if 1 ≤ n then gaussSum χ stdAddChar * (2 * (Real.pi : ℂ) * I) ^ n else 1

@[category API, AMS 11 14]
lemma period_ne_zero [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (n : ℤ) :
    period χ n ≠ 0 := by
  rw [period]
  split
  · exact mul_ne_zero hχ.gaussSum_ne_zero (zpow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero]))
  · exact one_ne_zero

/-- Galois conjugation as a permutation of the primitive Dirichlet characters modulo `N`. -/
noncomputable def galoisAction [NeZero N] :
    Gal(ℂ/ℚ) →* Equiv.Perm {χ : DirichletCharacter ℂ N // χ.IsPrimitive} where
  toFun σ := {
      toFun χ := ⟨galoisConj χ.1 σ, isPrimitive_galoisConj σ χ.2⟩
      invFun χ := ⟨galoisConj χ.1 σ⁻¹, isPrimitive_galoisConj σ⁻¹ χ.2⟩
      left_inv χ := by ext; simp
      right_inv χ := by ext; simp
  }
  map_one' := by ext; simp
  map_mul' σ τ := by ext; simp

/-- The Deligne family of primitive Dirichlet characters modulo `N`. -/
noncomputable def pkg (N : ℕ) [NeZero N] :
    Pkg {χ : DirichletCharacter ℂ N // χ.IsPrimitive} where
  L χ := DirichletCharacter.LFunction χ.1
  valueField χ := valueField χ.1
  weight _ := 0
  gammaShifts χ := if χ.1.Even then {0} else {1}
  period χ n := period χ.1 n
  galoisAction := galoisAction
  weight_galoisAction _ _ := rfl
  gammaShifts_galoisAction σ χ := by simp [galoisAction]
  valueField_isAlgebraic χ x hx :=
    IntermediateField.isAlgebraic_iff.mp <|
      ((IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic ℚ ℂ).mpr
        (by rintro _ ⟨a, rfl⟩; exact χ.1.isAlgebraic_apply a)).isAlgebraic ⟨x, hx⟩
  valueField_galoisAction σ χ := valueField_galoisConj σ χ.1
  period_ne_zero' χ n _ _ := period_ne_zero χ.2 n

/-- Deligne's conjecture for the critical values of Dirichlet L-functions:
`L(n, χ) / c(n, χ) ∈ ℚ(χ)` where `c(n, χ) = 1` if `n ≤ 0` and `c(n, χ) = G(χ)(2πi)ⁿ` if `1 ≤ n`. -/
@[category textbook, AMS 11 14, formal_proof using lean4 at
  "https://github.com/smmercuri/special-values/blob/e533378e0c16693103f8b7cd75aed33d2c6b2d33/SpecialValues/Deligne/GL1/Statement.lean#L166"]
theorem conjecture {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (h : χ.IsPrimitive) :
    (pkg N).Conjecture ⟨χ, h⟩ := by
  sorry

end GL1

end Deligne
