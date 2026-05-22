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

/-- Fundamental discriminants are those integers `D` that appear as discriminants of quadratic
fields.

`D` is a fundamental discriminant if it is either of the form `4m` for `m` congruent to `2` or `3`
mod `4` squarefree, or if it congruent to `1` mod `4` and squarefree. -/
def IsFundamentalDiscr (D : ℤ) : Prop :=
  4 ∣ D ∧ ¬ D / 4 ≡ 1 [ZMOD 4] ∧ Squarefree (D / 4) ∨ D ≠ 1 ∧ D ≡ 1 [ZMOD 4] ∧ Squarefree D

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

/--
A Lucas–Wieferich prime associated with $(a,b)$ is an odd prime $p$, not dividing $a^2 - 4b$, such
that $U_{p-\varepsilon}(a,b) \equiv 0 \pmod{p^2}$ where $U(a,b)$ is the Lucas sequence of the first
kind and $\varepsilon$ is the Legendre symbol $\left({\tfrac {a^2-4b}{p}}\right)$.
The discriminant of this number is the quantity $a^2 - 4b$. It is conjectured that there are
infinitely many Lucas–Wieferich primes of any given non-one fundamental discriminant.

TODO: Source this conjecture
-/
@[category research open, AMS 11]
theorem infinite_isWallSunSunPrime_of_disc_eq {D : ℤ} (hD : IsFundamentalDiscr D)
    (hD₁ : D ≠ 1) :
    {p : ℕ | ∃ a b, a ^ 2 - 4 * b = D ∧ IsLucasWieferichPrime a b p}.Infinite := by
  sorry

end WallSunSun
