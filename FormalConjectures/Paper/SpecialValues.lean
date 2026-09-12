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

/-- For an object with value field `ℚ` that the Galois action fixes, equivariance is already
contained in arithmeticity. -/
@[category API, AMS 11 14]
theorem IsArithmetic.isEquivariant_of_valueField_eq_bot {M : Ω} (h : F.IsArithmetic M)
    (hE : F.valueField M = ⊥) (hgal : ∀ σ : Gal(ℂ/ℚ), F.galoisAction σ M = M) :
    F.IsEquivariant M := fun σ n hn ↦ by
  rw [hgal σ]
  have hmem : F.normalizedValue M n ∈ (⊥ : IntermediateField ℚ ℂ) := hE ▸ h n hn
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hmem
  rw [← hq]
  exact σ.commutes q

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

/-
## The odd symmetric powers of an elliptic curve

Deligne's conjecture for `Sym^(2m+1) E`, `E` an elliptic curve over `ℚ`.
-/

namespace SymPow

open ComplexConjugate Filter Set
open scoped Real Topology

/-- The Gamma integer shifts of the archimedean factor of `Sym^k E`. These consist of
- shifts `-p` and `-p + 1`, for each `p` with `2 * p < k`;
- shift of the even member of `{-m, -m + 1}` for `k = 2m` even. -/
def shifts (k : ℕ) : Multiset ℤ :=
  ((Multiset.range ((k + 1) / 2)).bind fun p ↦ (-(p : ℤ)) ::ₘ {-(p : ℤ) + 1}) +
    if Even k then {-2 * ((k / 4 : ℕ) : ℤ)} else 0

@[category API, AMS 11 14]
lemma mem_shifts_iff {k : ℕ} {a : ℤ} :
    a ∈ shifts k ↔ (∃ p : ℕ, 2 * p < k ∧ (a = -(p : ℤ) ∨ a = -(p : ℤ) + 1)) ∨
      (Even k ∧ a = -2 * ((k / 4 : ℕ) : ℤ)) := by
  have hr : ∀ p : ℕ, p < (k + 1) / 2 ↔ 2 * p < k := fun p ↦ by lia
  rw [shifts, Multiset.mem_add]
  simp only [Multiset.mem_bind, Multiset.mem_range, Multiset.mem_cons, Multiset.mem_singleton, hr]
  split_ifs with h <;> simp [h]

@[category API, AMS 11 14]
lemma forall_mem_shifts_iff_of_odd {m : ℕ} {t : ℤ} :
    (∀ a ∈ shifts (2 * m + 1), Odd (t + a) ∨ 0 < t + a) ↔ (m : ℤ) + 1 ≤ t := by
  refine ⟨fun h ↦ ?_, fun ht a ha ↦ ?_⟩
  · have h₁ := h _ (mem_shifts_iff.mpr (.inl ⟨m, by lia, .inl rfl⟩))
    have h₂ := h _ (mem_shifts_iff.mpr (.inl ⟨m, by lia, .inr rfl⟩))
    simp only [Int.odd_iff] at h₁ h₂; lia
  · rcases mem_shifts_iff.mp ha with ⟨p, hp, hpa⟩ | ⟨hk, -⟩
    · rcases hpa with rfl | rfl <;> exact .inr (by lia)
    · rw [Nat.even_iff] at hk; lia

/-- The critical set of `Sym^(2m+1) E` is the single integer `m + 1`, for any package carrying
its weight and shifts. -/
@[category API, AMS 11 14]
theorem isCritical_iff_of_odd {Ω : Type*} (F : Pkg Ω) {M : Ω} {m : ℕ}
    (hw : F.weight M = 2 * m + 1) (hs : F.gammaShifts M = shifts (2 * m + 1)) (n : ℤ) :
    F.IsCritical M n ↔ n = m + 1 := by
  rw [Pkg.isCritical_iff, hs, hw, forall_mem_shifts_iff_of_odd, forall_mem_shifts_iff_of_odd]
  lia

section EulerFactor

open Polynomial

variable (k : ℕ) (a q : ℂ)

/-- The `k`-th symmetric power of the quadratic `1 - a T + q T ^ 2`: writing `α, β` for its
reciprocal roots (`α + β = a`, `α β = q`), this is `∏ i ∈ range (k + 1), (1 - α^i β^(k-i) T)`. -/
noncomputable def localPolynomial : ℂ[X] :=
  ∏ i ∈ Finset.range (k + 1),
    (1 - C ((quadraticRoots a q).1 ^ i * (quadraticRoots a q).2 ^ (k - i)) * X)

/-- `localPolynomial` computed from any pair of Frobenius eigenvalues with the given trace and
determinant. -/
@[category API, AMS 11 14]
theorem localPolynomial_eq_of_roots {α β : ℂ} (hadd : α + β = a) (hmul : α * β = q) :
    localPolynomial k a q = ∏ i ∈ Finset.range (k + 1), (1 - C (α ^ i * β ^ (k - i)) * X) := by
  have hswap (x y : ℂ) : ∏ i ∈ Finset.range (k + 1), (1 - C (x ^ i * y ^ (k - i)) * X)
      = ∏ i ∈ Finset.range (k + 1), (1 - C (y ^ i * x ^ (k - i)) * X) := by
    rw [← Finset.prod_range_reflect]
    exact Finset.prod_congr rfl fun i hi ↦ by grind
  have hroot : (α - (quadraticRoots a q).1) * (α - (quadraticRoots a q).2) = 0 := by
    linear_combination (-α) * quadraticRoots_add a q + quadraticRoots_mul a q + α * hadd - hmul
  rcases mul_eq_zero.mp hroot with h | h
  · have hβ : β = (quadraticRoots a q).2 := by
      linear_combination hadd - quadraticRoots_add a q - (sub_eq_zero.mp h)
    rw [localPolynomial, sub_eq_zero.mp h, hβ]
  · have hβ : β = (quadraticRoots a q).1 := by
      linear_combination hadd - quadraticRoots_add a q - (sub_eq_zero.mp h)
    rw [localPolynomial, sub_eq_zero.mp h, hβ]
    exact hswap _ _

@[category API, AMS 11 14]
theorem localPolynomial_one : localPolynomial 1 a q = 1 - C a * X + C q * X ^ 2 := by
  grind [localPolynomial, Finset.prod_range_succ, Finset.prod_range_zero, quadraticRoots_add,
    quadraticRoots_mul]

end EulerFactor

section LocalField

variable (k : ℕ) (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*}
  [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K)

/-- The local Euler factor of `Sym^k E` at a nonarchimedean place. -/
noncomputable def localEulerFactor : ArithmeticFunction ℂ :=
  let f := W.localPolynomial R
  .ofPowerSeries (Nat.card (IsLocalRing.ResidueField R))
    (PowerSeries.invOfUnit (localPolynomial k (-(f.coeff 1 : ℤ)) (f.coeff 2 : ℤ) : PowerSeries ℂ) 1)

end LocalField

section NumberField

open IsDedekindDomain NumberField

variable (k : ℕ) {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)

/-- The Euler product of the `Sym^k` `L`-function of a Weierstrass curve `W` over a number
field `K`. -/
noncomputable def eulerProduct : ArithmeticFunction ℂ :=
  ArithmeticFunction.eulerProduct fun p : HeightOneSpectrum (𝓞 K) ↦
    localEulerFactor k (p.adicCompletionIntegers K) (W.baseChange (p.adicCompletion K))

end NumberField

/-- `Λ` is the `Sym^k` `L`-function of the elliptic curve given by `W`: it is meromorphic on `ℂ`
in normal form, and on the half-plane `1 + k / 2 < re s` it is the sum of the Dirichlet series
`Deligne.SymPow.eulerProduct k W`. If such an object exists, then this structure determines it.
uniquely. This avoids the need to construct the meromorphic continuation. -/
structure IsLFunction (k : ℕ) (W : WeierstrassCurve ℚ) (Λ : ℂ → ℂ) : Prop where
  /-- `Λ` is meromorphic on `ℂ`, in the normal form that fixes its values at the poles. -/
  meromorphicNFOn : MeromorphicNFOn Λ univ
  /-- On the half-plane `1 + k / 2 < re s` the Dirichlet series converges to `Λ s`. -/
  lSeriesHasSum : ∀ s : ℂ, 1 + (k : ℝ) / 2 < s.re → LSeriesHasSum (eulerProduct k W) s (Λ s)

/-- The `Sym^k` `L`-function is determined by its Dirichlet series. -/
@[category API, AMS 11 14]
theorem IsLFunction.unique {k : ℕ} {W : WeierstrassCurve ℚ} {Λ₁ Λ₂ : ℂ → ℂ}
    (h₁ : IsLFunction k W Λ₁) (h₂ : IsLFunction k W Λ₂) : Λ₁ = Λ₂ := by
  have hopen : IsOpen {s : ℂ | 1 + (k : ℝ) / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hmem : (2 + (k : ℂ)) ∈ {s : ℂ | 1 + (k : ℝ) / 2 < s.re} := by
    simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.re_ofNat, Complex.natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) k]
  refine h₁.meromorphicNFOn.eq_of_eventuallyEq h₂.meromorphicNFOn
    (z₀ := 2 + (k : ℂ)) (eventually_of_mem (hopen.mem_nhds hmem) fun s hs ↦ ?_)
  exact (h₁.lSeriesHasSum s hs).LSeries_eq.symm.trans (h₂.lSeriesHasSum s hs).LSeries_eq

/-- The `Sym^k` `L`-series of an elliptic curve over `ℚ` continues meromorphically
to `ℂ`. At `k = 1` this is modularity (Wiles, Taylor–Wiles, Breuil–Conrad–Diamond–Taylor).
See J. Newton and J. Thorne, *Symmetric power functoriality for holomorphic modular forms, I and
II*, Publ. Math. IHÉS 134 (2021). -/
@[category research solved, AMS 11]
theorem exists_isLFunction (k : ℕ) (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    ∃ Λ, IsLFunction k W Λ := by
  sorry

/-- The exponent `(m + 1)(m + 1 + (-1)^m) / 2` of `Ω⁺` in Deligne's period of
`(Sym^(2m+1) E)(m + 1)`. -/
def realExponent (m : ℕ) : ℕ := if Even m then (m + 1) * (m + 2) / 2 else m * (m + 1) / 2

/-- The exponent `(m + 1)(m + 1 - (-1)^m) / 2` of `Ω⁻` in Deligne's period of
`(Sym^(2m+1) E)(m + 1)`. -/
def imagExponent (m : ℕ) : ℕ := if Even m then m * (m + 1) / 2 else (m + 1) * (m + 2) / 2

/-- Deligne's period `c⁺((Sym^(2m+1) E)(m + 1))`, up to `ℚˣ`, in terms of the real and
imaginary periods of `E`. -/
noncomputable def criticalPeriod (m : ℕ) (Ωre Ωim : ℂ) : ℂ :=
  Ωre ^ realExponent m * Ωim ^ imagExponent m / (2 * π * I) ^ (m * (m + 1) / 2)

/-- The period the statement divides by is nonzero. -/
@[category API, AMS 11 14]
theorem criticalPeriod_ne_zero {ℒ : PeriodPair} (m : ℕ)
    (hstab : ∀ z ∈ ℒ.lattice, conj z ∈ ℒ.lattice) :
    criticalPeriod m ℒ.realPeriod ℒ.imagPeriod ≠ 0 :=
  div_ne_zero (mul_ne_zero (pow_ne_zero _ (ℒ.realPeriod_ne_zero hstab))
    (pow_ne_zero _ (ℒ.imagPeriod_ne_zero hstab))) (pow_ne_zero _ Complex.two_pi_I_ne_zero)

/-- The parameters of the `Sym^(2m+1) E` Deligne package
- `W/ℚ` an elliptic curve `E` over `ℚ`
- `Λ` the `Sym^(2m+1)` `L`-function of `E`
- `ℒ` a period pair uniformising `W`
along with fields asserting their expected properties. -/
structure Obj (m : ℕ) where
  /-- A Weierstrass model of the elliptic curve. -/
  W : WeierstrassCurve ℚ
  /-- The `Sym^(2m+1)` `L`-function. -/
  Λ : ℂ → ℂ
  /-- The period lattice. -/
  ℒ : PeriodPair
  /-- `Λ` is the `Sym^(2m+1)` `L`-function of `E`. -/
  isLFunction : IsLFunction (2 * m + 1) W Λ
  /-- `ℒ` uniformises `W`. -/
  uniformises : ℒ.Uniformises W.g₂ W.g₃
  /-- The lattice is stable under complex conjugation. -/
  conj_mem : ∀ z ∈ ℒ.lattice, conj z ∈ ℒ.lattice

/-- The Deligne package of `Sym^(2m+1) E`. -/
noncomputable def pkg (m : ℕ) : Pkg (Obj m) where
  L M := M.Λ
  valueField _ := ⊥
  weight _ := 2 * m + 1
  gammaShifts _ := shifts (2 * m + 1)
  period M _ := criticalPeriod m M.ℒ.realPeriod M.ℒ.imagPeriod
  galoisAction := 1
  weight_galoisAction _ _ := rfl
  gammaShifts_galoisAction _ _ := rfl
  valueField_galoisAction _ _ := (IntermediateField.map_bot _).symm
  valueField_isAlgebraic _ _ hx := by
    obtain ⟨q, rfl⟩ := IntermediateField.mem_bot.mp hx
    exact isAlgebraic_algebraMap q
  period_ne_zero' M _ _ _ := criticalPeriod_ne_zero m M.conj_mem

variable {m : ℕ}

@[simp, category API, AMS 11 14]
theorem L_pkg (M : Obj m) : (pkg m).L M = M.Λ := rfl

@[simp, category API, AMS 11 14]
theorem weight_pkg (M : Obj m) : (pkg m).weight M = 2 * m + 1 := rfl

@[simp, category API, AMS 11 14]
theorem gammaShifts_pkg (M : Obj m) : (pkg m).gammaShifts M = shifts (2 * m + 1) := rfl

@[simp, category API, AMS 11 14]
theorem valueField_pkg (M : Obj m) : (pkg m).valueField M = ⊥ := rfl

@[simp, category API, AMS 11 14]
theorem galoisAction_pkg (σ : Gal(ℂ/ℚ)) (M : Obj m) : (pkg m).galoisAction σ M = M := rfl

@[simp, category API, AMS 11 14]
theorem period_pkg (M : Obj m) (n : ℤ) :
    (pkg m).period M n = criticalPeriod m M.ℒ.realPeriod M.ℒ.imagPeriod := rfl

/-- The framework's critical set for the package is the single integer `m + 1`. -/
@[category API, AMS 11 14]
theorem isCritical_pkg_iff (M : Obj m) (n : ℤ) : (pkg m).IsCritical M n ↔ n = (m : ℤ) + 1 :=
  isCritical_iff_of_odd _ (weight_pkg M) (gammaShifts_pkg M) n

/-- **Deligne's conjecture for `Sym^(2m+1) E`**, for every elliptic curve `E` over `ℚ`:
`Λ(m + 1)` divided by `Deligne.SymPow.criticalPeriod` is rational, where `Λ` is the `Sym^(2m+1)`
`L`-function of `E`.

Known cases encompass `m = 0` and `m = 1`, while for `m ≥ 2` it is known only when `E` has
complex multiplication, and is open otherwise. -/
@[category research open, AMS 11 14]
theorem conjecture (m : ℕ) (M : Obj m) : (pkg m).Conjecture M := by
  sorry

/-- The known case `m = 0`: `L(E, 1) / Ω⁺ ∈ ℚ`. A theorem, by modularity
(Wiles, Taylor–Wiles, Breuil–Conrad–Diamond–Taylor) and Shimura's period theorem
for the modular form attached to `E` (Manin). -/
@[category research solved, AMS 11 14]
theorem conjecture.variants.zero (M : Obj 0) : (pkg 0).Conjecture M := by
  sorry

/-- The known case `m = 1`, Deligne's conjecture for `Sym³ E` at its critical point `2`:
`L(Sym³ E, 2) · 2πi / (Ω⁺ (Ω⁻)³) ∈ ℚ`. A theorem of Garrett–Harris, via the triple product
`L`-function `L(s, φ × φ × φ)`; reproved by Kim–Shahidi. See P. Garrett and M. Harris,
*Special values of triple product L-functions*, Amer. J. Math. 115 (1993), and H. Kim and F.
Shahidi, *Symmetric cube L-functions for GL₂ are entire*, Ann. of Math. 150 (1999). -/
@[category research solved, AMS 11 14]
theorem conjecture.variants.one (M : Obj 1) : (pkg 1).Conjecture M := by
  sorry

end SymPow

end Deligne
