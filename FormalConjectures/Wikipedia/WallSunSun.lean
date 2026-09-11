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
import FormalConjecturesUtil

/-!
# Infinitude of Wall–Sun–Sun primes

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Wall%E2%80%93Sun%E2%80%93Sun_prime)
-/

open Algebra (IsQuadraticExtension)
open NumberField

namespace QuadraticAlgebra
variable {d : ℤ} [Fact <| Squarefree d] [Fact <| d ≠ 1]

/-- The discriminant of `ℚ[√d]` for `d ≥ 2` squarefree congruent to 1 mod 4 is `d`. -/
@[category textbook, AMS 11, simp]
lemma discr_rat_of_modEq_one (hd₄ : d ≡ 1 [ZMOD 4]) : discr (QuadraticAlgebra ℚ d 0) = d := by
  sorry

/-- The discriminant of `ℚ[√d]` for `d ≥ 2` squarefree not congruent to 1 mod 4 is `4 * d`. -/
@[category textbook, AMS 11, simp]
lemma discr_rat_of_not_modEq_one (hd₄ : ¬ d ≡ 1 [ZMOD 4]) :
    discr (QuadraticAlgebra ℚ d 0) = 4 * d := by
  sorry

end QuadraticAlgebra

namespace Algebra
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable (K L) in
/-- A quadratic algebra `L` over a field `K` is isomorphic to the explicit quadratic algebra
`QuadraticAlgebra K a b` for some `a b : K`. -/
@[category textbook, AMS 11]
lemma exists_quadraticAlgebra_of_isQuadraticExtension [IsQuadraticExtension K L] :
    ∃ a b, Nonempty (L ≃ₐ[K] QuadraticAlgebra K a b) := by
  sorry

/-- An algebra `L` is quadratic over a field `K` iff it is isomorphic to the explicit quadratic
algebra `QuadraticAlgebra K a b` for some `a b : K`. -/
@[category textbook, AMS 11]
lemma isQuadraticExtension_iff_exists_quadraticAlgebra :
    IsQuadraticExtension K L ↔ ∃ a b, Nonempty (L ≃ₐ[K] QuadraticAlgebra K a b) where
  mp _ := exists_quadraticAlgebra_of_isQuadraticExtension ..
  mpr := by rintro ⟨a, b, ⟨e⟩⟩; sorry

end Algebra

namespace NumberField
variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/-- A quadratic number field `K` is isomorphic to the explicit quadratic field
`QuadraticAlgebra ℚ d 0` for some squarefree `d : ℤ` not equal to 1. -/
@[category textbook, AMS 11]
lemma exists_quadraticAlgebra_of_isQuadraticExtension [IsQuadraticExtension ℚ K] :
    ∃ d ≠ (1 : ℤ), Squarefree d ∧ Nonempty (K ≃+* QuadraticAlgebra ℚ d 0) := by
  sorry

/-- A number field `K` is quadratic iff it is isomorphic to the explicit quadratic field
`QuadraticAlgebra ℚ d 0` for some squarefree `d : ℤ` not equal to 1. -/
@[category textbook, AMS 11]
lemma isQuadraticExtension_iff_exists_quadraticAlgebra :
    IsQuadraticExtension ℚ K ↔
      ∃ d ≠ (1 : ℤ), Squarefree d ∧ Nonempty (K ≃+* QuadraticAlgebra ℚ d 0) where
  mp _ := exists_quadraticAlgebra_of_isQuadraticExtension _
  mpr := by rintro ⟨d, hd₁, hd, ⟨e⟩⟩; sorry

/-- An integer `D` is a fundamental discriminant iff it is the discriminant of the explicit
quadratic field `QuadraticAlgebra ℚ d 0` for some squarefree `d : ℤ` not equal to 1. -/
@[category textbook, AMS 11]
lemma isFundamentalDiscr_iff_exists_discr_quadraticAlgebra {D : ℤ} :
    IsFundamentalDiscr D ↔ ∃ (d : ℤ) (_ : Fact <| d ≠ 1) (_ : Fact <| Squarefree d),
      discr (QuadraticAlgebra ℚ d 0) = D where
  mp := by
    rintro (⟨⟨d, rfl⟩, hD₄, hD⟩ | ⟨hD₁, hD₄, hD⟩)
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀] at hD hD₄
      have : Fact <| d ≠ 1 := ⟨by rintro rfl; simp at hD₄⟩
      have : Fact <| Squarefree d := ⟨hD⟩
      exact ⟨d, inferInstance, inferInstance, QuadraticAlgebra.discr_rat_of_not_modEq_one hD₄⟩
    · have : Fact <| D ≠ 1 := ⟨hD₁⟩
      have : Fact <| Squarefree D := ⟨hD⟩
      exact ⟨D, inferInstance, inferInstance, QuadraticAlgebra.discr_rat_of_modEq_one hD₄⟩
  mpr := by
    rintro ⟨d, _, _, rfl⟩; by_cases hd₄ : d ≡ 1 [ZMOD 4] <;> simp [*, IsFundamentalDiscr, Fact.out]

/-- An integer `D` is a fundamental discriminant iff it is the discriminant of some number field. -/
@[category textbook, AMS 11]
lemma isFundamentalDiscr_iff_exists_discr_numberField {D : ℤ} :
    IsFundamentalDiscr D ↔
      ∃ (K : Type) (_ : Field K) (_ : NumberField K), IsQuadraticExtension ℚ K ∧ discr K = D := by
  rw [isFundamentalDiscr_iff_exists_discr_quadraticAlgebra]
  constructor
  · rintro ⟨d, _, _, rfl⟩
    exact ⟨_, inferInstance, inferInstance, inferInstance, rfl⟩
  · rintro ⟨K, _, _, _, rfl⟩
    obtain ⟨d, hd₁, hd, ⟨e⟩⟩ := exists_quadraticAlgebra_of_isQuadraticExtension K
    have : Fact <| d ≠ 1 := ⟨hd₁⟩
    have : Fact <| Squarefree d := ⟨hd⟩
    exact ⟨d, inferInstance, inferInstance, discr_eq_discr_of_ringEquiv _ e.symm⟩

end NumberField

namespace WallSunSun

open scoped NumberTheorySymbols

/--
A prime $p$ is a Wall–Sun–Sun prime if and only if $L_p \equiv 1 \pmod{p^2}$, where $L_p$ is the
$p$-th Lucas number. It is conjectured that there is at least one Wall–Sun–Sun prime.
-/
@[category research open, AMS 11]
theorem exists_isWallSunSunPrime : ∃ p, IsWallSunSunPrime p := by
  sorry

/--
A prime $p$ is a Wall–Sun–Sun prime if and only if $L_p \equiv 1 \pmod{p^2}$, where $L_p$ is the
$p$-th Lucas number. It is conjectured that there are infinitely many Wall-Sun-Sun primes.
-/
@[category research open, AMS 11]
theorem infinite_isWallSunSunPrime : {p : ℕ | IsWallSunSunPrime p}.Infinite := by
  sorry

@[category API, AMS 11]
private lemma lucasSequence_dvd_U_two_mul (P Q : ℤ) :
    ∀ k : ℕ, P ∣ LucasSequence.U P Q (2 * k) := by
  intro k
  induction k with
  | zero => simp [LucasSequence.U]
  | succ k ih =>
      rw [Nat.mul_succ]
      simp only [LucasSequence.U]
      exact dvd_sub (dvd_mul_right P _) (dvd_mul_of_dvd_right ih Q)

@[category API, AMS 11]
private lemma gcd_coe_prime_eq_one {D : ℤ} {p : ℕ} (hp : p.Prime)
    (hpd : ¬ (p : ℤ) ∣ D) : D.gcd (p : ℤ) = 1 := by
  have hpnat : ¬ p ∣ D.natAbs := by
    intro h
    apply hpd
    rw [← Int.natAbs_dvd_natAbs]
    simpa using h
  rw [Int.gcd_eq_natAbs]
  simpa [Nat.gcd_comm] using (hp.coprime_iff_not_dvd.mpr hpnat).gcd_eq_one

@[category API, AMS 11]
private lemma isLucasWieferichPrime_of_sq_dvd_a {a b D : ℤ} {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hdisc : a ^ 2 - 4 * b = D) (hpd : ¬ (p : ℤ) ∣ D)
    (ha : (p : ℤ) ^ 2 ∣ a) : IsLucasWieferichPrime a b p := by
  refine ⟨hp, hodd, ?_, ?_⟩
  · simpa [hdisc] using hpd
  · rw [Int.modEq_zero_iff_dvd]
    have hgcd : D.gcd (p : ℤ) = 1 := gcd_coe_prime_eq_one hp hpd
    have hJ : J(D | p) = 1 ∨ J(D | p) = -1 := jacobiSym.eq_one_or_neg_one hgcd
    rcases hodd with ⟨k, hk⟩
    rcases hJ with hJ | hJ
    · have hindex : ((p : ℤ) - J(a ^ 2 - 4 * b | p)).toNat = 2 * k := by
        rw [hdisc, hJ, hk]
        omega
      rw [hindex]
      exact ha.trans (lucasSequence_dvd_U_two_mul a b k)
    · have hindex : ((p : ℤ) - J(a ^ 2 - 4 * b | p)).toNat = 2 * (k + 1) := by
        rw [hdisc, hJ, hk]
        omega
      rw [hindex]
      exact ha.trans (lucasSequence_dvd_U_two_mul a b (k + 1))

@[category API, AMS 11]
private lemma exists_parameters {D : ℤ} {p : ℕ}
    (hmod : (4 : ℤ) ∣ D ∨ D ≡ 1 [ZMOD 4]) (hodd : Odd p) :
    ∃ a b : ℤ, a ^ 2 - 4 * b = D ∧ (p : ℤ) ^ 2 ∣ a := by
  rcases hmod with hfour | hone
  · rcases hfour with ⟨d, rfl⟩
    refine ⟨2 * (p : ℤ) ^ 2, (p : ℤ) ^ 4 - d, by ring, ?_⟩
    exact dvd_mul_left _ _
  · rcases hodd with ⟨k, rfl⟩
    rcases hone.dvd with ⟨c, hc⟩
    refine ⟨((2 * k + 1 : ℕ) : ℤ) ^ 2,
      4 * (k : ℤ) ^ 4 + 8 * (k : ℤ) ^ 3 + 6 * (k : ℤ) ^ 2 + 2 * (k : ℤ) + c,
      ?_, dvd_refl _⟩
    push_cast
    nlinarith

/--
A Lucas–Wieferich prime associated with $(a,b)$ is an odd prime $p$, not dividing $a^2 - 4b$, such
that $U_{p-\varepsilon}(a,b) \equiv 0 \pmod{p^2}$ where $U(a,b)$ is the Lucas sequence of the first
kind and $\varepsilon$ is the Legendre symbol $\left({\tfrac {a^2-4b}{p}}\right)$.
The discriminant of this number is the quantity $a^2 - 4b$.

In the statement below, `a` and `b` are existentially quantified separately for every prime `p`.
This makes the literal statement elementary: one can choose `a` to be divisible by `p²`, while
choosing `b` so that `a² - 4b = D`. See `infinite_isLucasWieferichPrime_fixed_parameters` for the
intended open conjecture, in which the Lucas sequence is fixed before `p` varies.
-/
@[category research solved, AMS 11]
theorem infinite_isWallSunSunPrime_of_disc_eq {D : ℤ} (hD : IsFundamentalDiscr D)
    (hD₁ : D ≠ 1) :
    {p : ℕ | ∃ a b, a ^ 2 - 4 * b = D ∧ IsLucasWieferichPrime a b p}.Infinite := by
  have hDzero : D ≠ 0 := by
    intro h
    subst D
    simp [IsFundamentalDiscr] at hD
  have hmod : (4 : ℤ) ∣ D ∨ D ≡ 1 [ZMOD 4] := by
    rcases hD with h | h
    · exact Or.inl h.1
    · exact Or.inr h.2.1
  let B := max D.natAbs 2
  have hinf : ({p : ℕ | p.Prime} \ Set.Iic B).Infinite :=
    Nat.infinite_setOfPred_prime.sdiff (Set.finite_Iic B)
  apply hinf.mono
  intro p hpB
  rcases hpB with ⟨hp, hpB⟩
  simp only [Set.mem_ofPred_eq] at hp
  simp only [Set.mem_Iic, not_le] at hpB
  have hpD : D.natAbs < p := lt_of_le_of_lt (le_max_left _ _) hpB
  have hp2 : 2 < p := lt_of_le_of_lt (le_max_right _ _) hpB
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hpd : ¬ (p : ℤ) ∣ D := by
    intro h
    have := Int.natAbs_le_of_dvd_ne_zero h hDzero
    simp only [Int.natAbs_natCast] at this
    omega
  obtain ⟨a, b, hab, ha⟩ := exists_parameters hmod hodd
  exact ⟨a, b, hab, isLucasWieferichPrime_of_sq_dvd_a hp hodd hab hpd ha⟩

/-- The intended Lucas--Wieferich infinitude conjecture: fix the Lucas sequence parameters
`(a,b)` first, require their discriminant to be a non-one fundamental discriminant, and then ask
for infinitely many associated Lucas--Wieferich primes. -/
@[category research open, AMS 11]
theorem infinite_isLucasWieferichPrime_fixed_parameters {a b : ℤ}
    (hD : IsFundamentalDiscr (a ^ 2 - 4 * b)) (hD₁ : a ^ 2 - 4 * b ≠ 1) :
    {p : ℕ | IsLucasWieferichPrime a b p}.Infinite := by
  sorry

end WallSunSun
