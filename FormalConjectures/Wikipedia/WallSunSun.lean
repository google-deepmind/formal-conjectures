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

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Wall%E2%80%93Sun%E2%80%93Sun_prime)
- [EJ10] A.-S. Elsenhans and J. Jahnel, *The Fibonacci sequence modulo $p^2$ – An investigation by
  computer for $p < 10^{14}$*, [arXiv:1006.0824](https://arxiv.org/abs/1006.0824)
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

/-- An earlier formulation of `infinite_isWallSunSunPrime_of_disc_eq`, which chose the Lucas
parameters $(a, b)$ separately for every prime $p$, was degenerate: it is provable. -/
@[category test, AMS 11]
theorem infinite_isWallSunSunPrime_of_disc_eq_varying_parameters {D : ℤ}
    (hD : IsFundamentalDiscr D) :
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
  exact ⟨a, b, hab, IsLucasWieferichPrime.of_sq_dvd hp hodd (hab ▸ hpd) ha⟩

/--
Let $K$ be a real quadratic field of discriminant $D$ and let $\varepsilon$ be a fundamental unit
of $K$. Following [EJ10, Remark 2.2.8], an odd prime $p \nmid D$ is a Wall–Sun–Sun prime for $K$
if, in $\mathcal{O}_K$, $\varepsilon^{p-1} \equiv 1 \pmod{p^2}$ when
$\left(\tfrac{D}{p}\right) = 1$, and $\varepsilon^{2p+2} \equiv 1 \pmod{p^2}$ when
$\left(\tfrac{D}{p}\right) = -1$. Both exponents are even, so the condition does not depend on the
choice of $\varepsilon$, and it is equivalent to asking the same congruence for every unit of $K$.
For $K = \mathbb{Q}(\sqrt{5})$ and $\varepsilon = \frac{1 + \sqrt{5}}{2}$ these are the classical
Wall–Sun–Sun primes other than $2$ and $5$ [EJ10, Proposition 2.2.6].

It is conjectured that for every fundamental discriminant $D \neq 1$ there are infinitely many
Wall–Sun–Sun primes with discriminant $D$ (Wikipedia; [EJ10, §4.1] gives the heuristic for
$\mathbb{Q}(\sqrt{5})$). It is stated here for $D > 0$ only. Wikipedia's sentence also covers
$D < 0$, but [EJ10] gives the definition above only for real quadratic fields, and its literal
extension to imaginary quadratic fields is degenerate: there every unit is a root of unity of
order dividing $4$ or $6$, and that order divides the relevant exponent $p - 1$ or $2p + 2$ for
every odd prime $p \nmid D$.
-/
@[category research open, AMS 11]
theorem infinite_isWallSunSunPrime_of_disc_eq {K : Type*} [Field K] [NumberField K]
    [IsQuadraticExtension ℚ K] [IsTotallyReal K] {D : ℤ} (hD : discr K = D) :
    {p : ℕ | p.Prime ∧ Odd p ∧ ¬ (p : ℤ) ∣ D ∧ ∀ ε : (𝓞 K)ˣ,
      (p : 𝓞 K) ^ 2 ∣ (ε : 𝓞 K) ^ (if J(D | p) = 1 then p - 1 else 2 * p + 2) - 1}.Infinite := by
  sorry

end WallSunSun
